<?php declare(strict_types = 1);

namespace PHPStan\Analyser;

use function is_object;
use PhpParser\Node;
use PhpParser\Node\Arg;
use PhpParser\Node\Expr;
use PhpParser\Node\Expr\Array_;
use PhpParser\Node\Expr\ArrayDimFetch;
use PhpParser\Node\Expr\ArrayItem;
use PhpParser\Node\Expr\Assign;
use PhpParser\Node\Expr\AssignRef;
use PhpParser\Node\Expr\BinaryOp;
use PhpParser\Node\Expr\BinaryOp\BooleanAnd;
use PhpParser\Node\Expr\BinaryOp\BooleanOr;
use PhpParser\Node\Expr\BinaryOp\Coalesce;
use PhpParser\Node\Expr\BooleanNot;
use PhpParser\Node\Expr\Cast;
use PhpParser\Node\Expr\ErrorSuppress;
use PhpParser\Node\Expr\Exit_;
use PhpParser\Node\Expr\FuncCall;
use PhpParser\Node\Expr\Instanceof_;
use PhpParser\Node\Expr\Isset_;
use PhpParser\Node\Expr\List_;
use PhpParser\Node\Expr\MethodCall;
use PhpParser\Node\Expr\New_;
use PhpParser\Node\Expr\Print_;
use PhpParser\Node\Expr\PropertyFetch;
use PhpParser\Node\Expr\StaticCall;
use PhpParser\Node\Expr\StaticPropertyFetch;
use PhpParser\Node\Expr\Ternary;
use PhpParser\Node\Expr\Variable;
use PhpParser\Node\Name;
use PhpParser\Node\Stmt\Break_;
use PhpParser\Node\Stmt\Catch_;
use PhpParser\Node\Stmt\Class_;
use PhpParser\Node\Stmt\Continue_;
use PhpParser\Node\Stmt\Do_;
use PhpParser\Node\Stmt\Echo_;
use PhpParser\Node\Stmt\For_;
use PhpParser\Node\Stmt\Foreach_;
use PhpParser\Node\Stmt\If_;
use PhpParser\Node\Stmt\Return_;
use PhpParser\Node\Stmt\Static_;
use PhpParser\Node\Stmt\StaticVar;
use PhpParser\Node\Stmt\Switch_;
use PhpParser\Node\Stmt\Throw_;
use PhpParser\Node\Stmt\TryCatch;
use PhpParser\Node\Stmt\Unset_;
use PhpParser\Node\Stmt\While_;
use PHPStan\Broker\Broker;
use PHPStan\File\FileHelper;
use PHPStan\Node\InClassMethodNode;
use PHPStan\Parser\Parser;
use PHPStan\PhpDoc\PhpDocBlock;
use PHPStan\PhpDoc\Tag\ParamTag;
use PHPStan\Reflection\ClassReflection;
use PHPStan\Reflection\ParametersAcceptorSelector;
use PHPStan\ShouldNotHappenException;
use PHPStan\TrinaryLogic;
use PHPStan\Type\ArrayType;
use PHPStan\Type\CommentHelper;
use PHPStan\Type\Constant\ConstantArrayType;
use PHPStan\Type\Constant\ConstantArrayTypeBuilder;
use PHPStan\Type\Constant\ConstantBooleanType;
use PHPStan\Type\Constant\ConstantIntegerType;
use PHPStan\Type\Constant\ConstantStringType;
use PHPStan\Type\ConstantScalarType;
use PHPStan\Type\ErrorType;
use PHPStan\Type\FileTypeMapper;
use PHPStan\Type\IntegerType;
use PHPStan\Type\MixedType;
use PHPStan\Type\ObjectType;
use PHPStan\Type\StringType;
use PHPStan\Type\Type;
use PHPStan\Type\TypeCombinator;
use PHPStan\Type\TypeUtils;
use PHPStan\Type\UnionType;

class NodeScopeResolver
{

	private const LOOP_SCOPE_ITERATIONS = 3;

	/** @var \PHPStan\Broker\Broker */
	private $broker;

	/** @var \PHPStan\Parser\Parser */
	private $parser;

	/** @var \PHPStan\Type\FileTypeMapper */
	private $fileTypeMapper;

	/** @var \PHPStan\File\FileHelper */
	private $fileHelper;

	/** @var \PHPStan\Analyser\TypeSpecifier */
	private $typeSpecifier;

	/** @var bool */
	private $polluteScopeWithLoopInitialAssignments;

	/** @var bool */
	private $polluteCatchScopeWithTryAssignments;

	/** @var bool */
	private $polluteScopeWithAlwaysIterableForeach;

	/** @var string[][] className(string) => methods(string[]) */
	private $earlyTerminatingMethodCalls;

	/** @var \PHPStan\Reflection\ClassReflection|null */
	private $anonymousClassReflection;

	/** @var bool[] filePath(string) => bool(true) */
	private $analysedFiles;

	/**
	 * @param Broker $broker
	 * @param Parser $parser
	 * @param FileTypeMapper $fileTypeMapper
	 * @param FileHelper $fileHelper
	 * @param TypeSpecifier $typeSpecifier
	 * @param bool $polluteScopeWithLoopInitialAssignments
	 * @param bool $polluteCatchScopeWithTryAssignments
	 * @param bool $polluteScopeWithAlwaysIterableForeach
	 * @param string[][] $earlyTerminatingMethodCalls className(string) => methods(string[])
	 */
	public function __construct(
		Broker $broker,
		Parser $parser,
		FileTypeMapper $fileTypeMapper,
		FileHelper $fileHelper,
		TypeSpecifier $typeSpecifier,
		bool $polluteScopeWithLoopInitialAssignments,
		bool $polluteCatchScopeWithTryAssignments,
		bool $polluteScopeWithAlwaysIterableForeach,
		array $earlyTerminatingMethodCalls
	)
	{
		$this->broker = $broker;
		$this->parser = $parser;
		$this->fileTypeMapper = $fileTypeMapper;
		$this->fileHelper = $fileHelper;
		$this->typeSpecifier = $typeSpecifier;
		$this->polluteScopeWithLoopInitialAssignments = $polluteScopeWithLoopInitialAssignments;
		$this->polluteCatchScopeWithTryAssignments = $polluteCatchScopeWithTryAssignments;
		$this->polluteScopeWithAlwaysIterableForeach = $polluteScopeWithAlwaysIterableForeach;
		$this->earlyTerminatingMethodCalls = $earlyTerminatingMethodCalls;
	}

	/**
	 * @param string[] $files
	 */
	public function setAnalysedFiles(array $files): void
	{
		$this->analysedFiles = array_fill_keys($files, true);
	}

	/**
	 * @param \PhpParser\Node[] $nodes
	 * @param \PHPStan\Analyser\Scope $scope
	 * @param \Closure(\PhpParser\Node $node, Scope $scope): void $nodeCallback
	 */
	public function processNodes(
		array $nodes,
		Scope $scope,
		\Closure $nodeCallback
	): void
	{
		foreach ($nodes as $i => $node) {
			if (!$node instanceof Node\Stmt) {
				continue;
			}

			$statementResult = $this->processStmtNode($node, $scope, $nodeCallback);
			if ($statementResult->isAlwaysTerminating()) {
				// todo virtual dead code node
				// todo test various pollute* settings
				break;
			}

			$scope = $statementResult->getScope();
		}
	}

	/**
	 * @param \PhpParser\Node\Stmt[] $stmts
	 * @param \PHPStan\Analyser\Scope $scope
	 * @param \Closure(\PhpParser\Node $node, Scope $scope): void $nodeCallback
	 * @return StatementResult
	 */
	public function processStmtNodes(
		array $stmts,
		Scope $scope,
		\Closure $nodeCallback
	): StatementResult
	{
		$exitPoints = [];
		foreach ($stmts as $stmt) {
			$statementResult = $this->processStmtNode($stmt, $scope, $nodeCallback);
			$exitPoints = array_merge($exitPoints, $statementResult->getExitPoints());
			if ($statementResult->isAlwaysTerminating()) {
				return new StatementResult(
					$statementResult->getScope(),
					$statementResult->getAlwaysTerminatingStatements(),
					$exitPoints
				);
			}

			$scope = $statementResult->getScope();
		}

		return new StatementResult($scope, [], $exitPoints);
	}

	/**
	 * @param \PhpParser\Node\Stmt $stmt
	 * @param \PHPStan\Analyser\Scope $scope
	 * @param \Closure(\PhpParser\Node $node, Scope $scope): void $nodeCallback
	 * @return StatementResult
	 */
	private function processStmtNode(
		Node\Stmt $stmt,
		Scope $scope,
		\Closure $nodeCallback
	): StatementResult
	{
		$nodeCallback($stmt, $scope);

		// todo handle all stmt descendants
		if ($stmt instanceof Node\Stmt\Declare_) {
			foreach ($stmt->declares as $declare) {
				$nodeCallback($declare, $scope);
				$nodeCallback($declare->value, $scope);
				if (
					$declare->key->name === 'strict_types'
					&& $declare->value instanceof Node\Scalar\LNumber
					&& $declare->value->value === 1
				) {
					$scope = $scope->enterDeclareStrictTypes();
				}
			}
		} elseif ($stmt instanceof Node\Stmt\Function_) {
			[$phpDocParameterTypes, $phpDocReturnType, $phpDocThrowType, $isDeprecated, $isInternal, $isFinal] = $this->getPhpDocs($scope, $stmt);

			foreach ($stmt->params as $param) {
				$this->processParamNode($param, $scope, $nodeCallback);
			}

			if ($stmt->returnType !== null) {
				$nodeCallback($stmt->returnType, $scope);
			}

			$functionScope = $scope->enterFunction(
				$stmt,
				$phpDocParameterTypes,
				$phpDocReturnType,
				$phpDocThrowType,
				$isDeprecated,
				$isInternal,
				$isFinal
			);
			$this->processStmtNodes($stmt->stmts, $functionScope, $nodeCallback);
		} elseif ($stmt instanceof Node\Stmt\ClassMethod) {
			[$phpDocParameterTypes, $phpDocReturnType, $phpDocThrowType, $isDeprecated, $isInternal, $isFinal] = $this->getPhpDocs($scope, $stmt);

			foreach ($stmt->params as $param) {
				$this->processParamNode($param, $scope, $nodeCallback);
			}

			if ($stmt->returnType !== null) {
				$nodeCallback($stmt->returnType, $scope);
			}

			$methodScope = $scope->enterClassMethod(
				$stmt,
				$phpDocParameterTypes,
				$phpDocReturnType,
				$phpDocThrowType,
				$isDeprecated,
				$isInternal,
				$isFinal
			);
			$nodeCallback(new InClassMethodNode($stmt), $methodScope);

			if ($stmt->stmts !== null) {
				$this->processStmtNodes($stmt->stmts, $methodScope, $nodeCallback);
			}
		} elseif ($stmt instanceof Echo_) {
			foreach ($stmt->exprs as $echoExpr) {
				$scope = $this->processExprNode($echoExpr, $scope, $nodeCallback, 1);
			}
		} elseif ($stmt instanceof Return_) {
			if ($stmt->expr !== null) {
				$scope = $this->processExprNode($stmt->expr, $scope, $nodeCallback, 1);
			}

			return new StatementResult($scope, [$stmt], [
				new StatementExitPoint($stmt, $scope),
			]);
		} elseif ($stmt instanceof Continue_) {
			if ($stmt->num !== null) {
				$scope = $this->processExprNode($stmt->num, $scope, $nodeCallback, 1);
			}

			return new StatementResult($scope, [$stmt], [
				new StatementExitPoint($stmt, $scope),
			]);
		} elseif ($stmt instanceof Break_) {
			if ($stmt->num !== null) {
				$scope = $this->processExprNode($stmt->num, $scope, $nodeCallback, 1);
			}

			return new StatementResult($scope, [$stmt], [
				new StatementExitPoint($stmt, $scope),
			]);
		} elseif ($stmt instanceof Node\Stmt\Expression) {
			$earlyTerminationExpr = $this->findEarlyTerminatingExpr($stmt->expr, $scope);
			$scope = $this->processExprNode($stmt->expr, $scope, $nodeCallback, 0);
			$scope = $scope->filterBySpecifiedTypes($this->typeSpecifier->specifyTypesInCondition(
				$scope,
				$stmt->expr,
				TypeSpecifierContext::createNull()
			));
			if ($earlyTerminationExpr !== null) {
				return new StatementResult($scope, [$stmt], [
					new StatementExitPoint($stmt, $scope),
				]);
			}
		} elseif ($stmt instanceof Node\Stmt\Namespace_) {
			if ($stmt->name !== null) {
				$scope = $scope->enterNamespace($stmt->name->toString());
			}

			$scope = $this->processStmtNodes($stmt->stmts, $scope, $nodeCallback)->getScope();
		} elseif ($stmt instanceof Node\Stmt\Trait_) {
			return new StatementResult($scope, [], []);
		} elseif ($stmt instanceof Node\Stmt\ClassLike) {
			if (isset($stmt->namespacedName)) {
				$classScope = $scope->enterClass($this->broker->getClass((string) $stmt->namespacedName));
			} elseif ($stmt instanceof Class_) {
				$classScope = $scope->enterAnonymousClass($this->broker->getAnonymousClassReflection($stmt, $scope));
			} else {
				throw new ShouldNotHappenException();
			}

			$this->processStmtNodes($stmt->stmts, $classScope, $nodeCallback);
		} elseif ($stmt instanceof Node\Stmt\Property) {
			foreach ($stmt->props as $prop) {
				$this->processStmtNode($prop, $scope, $nodeCallback);
			}

			if ($stmt->type !== null) {
				$nodeCallback($stmt->type, $scope);
			}
		} elseif ($stmt instanceof Node\Stmt\PropertyProperty) {
			if ($stmt->default !== null) {
				$this->processExprNode($stmt->default, $scope, $nodeCallback, 1);
			}
		} elseif ($stmt instanceof Throw_) {
			$scope = $this->processExprNode($stmt->expr, $scope, $nodeCallback, 1);
			return new StatementResult($scope, [$stmt], [
				new StatementExitPoint($stmt, $scope),
			]);
		} elseif ($stmt instanceof If_) {
			$conditionType = $scope->getType($stmt->cond)->toBoolean();
			$scope = $this->processExprNode($stmt->cond, $scope, $nodeCallback, 1);
			$exitPoints = [];
			$finalScope = null;
			$alwaysTerminatingStatements = [];
			$alwaysTerminating = true;

			if (!$conditionType instanceof ConstantBooleanType || $conditionType->getValue()) {
				$branchScopeStatementResult = $this->processStmtNodes($stmt->stmts, $scope->filterByTruthyValue($stmt->cond), $nodeCallback);
				$exitPoints = $branchScopeStatementResult->getExitPoints();
				$branchScope = $branchScopeStatementResult->getScope();
				$finalScope = $branchScopeStatementResult->isAlwaysTerminating() ? null : $branchScope;
				$alwaysTerminating = $branchScopeStatementResult->isAlwaysTerminating();
				if ($branchScopeStatementResult->isAlwaysTerminating()) {
					$alwaysTerminatingStatements = array_merge($alwaysTerminatingStatements, $branchScopeStatementResult->getAlwaysTerminatingStatements());
				}
			}

			if (!$conditionType instanceof ConstantBooleanType || !$conditionType->getValue()) {
				$scope = $scope->filterByFalseyValue($stmt->cond);
				$lastElseIfConditionIsTrue = false;

				foreach ($stmt->elseifs as $elseif) {
					$elseIfConditionType = $scope->getType($elseif->cond)->toBoolean();
					if (
						$elseIfConditionType instanceof ConstantBooleanType
						&& !$elseIfConditionType->getValue()
					) {
						continue;
					}
					$scope = $this->processExprNode($elseif->cond, $scope, $nodeCallback, 1);
					$branchScopeStatementResult = $this->processStmtNodes($elseif->stmts, $scope->filterByTruthyValue($elseif->cond), $nodeCallback);
					$exitPoints = array_merge($exitPoints, $branchScopeStatementResult->getExitPoints());
					$branchScope = $branchScopeStatementResult->getScope();
					$finalScope = $branchScopeStatementResult->isAlwaysTerminating() ? $finalScope : $branchScope->mergeWith($finalScope);
					$alwaysTerminating = $alwaysTerminating && $branchScopeStatementResult->isAlwaysTerminating();
					if ($branchScopeStatementResult->isAlwaysTerminating()) {
						$alwaysTerminatingStatements = array_merge($alwaysTerminatingStatements, $branchScopeStatementResult->getAlwaysTerminatingStatements());
					}

					if (
						$elseIfConditionType instanceof ConstantBooleanType
						&& $elseIfConditionType->getValue()
					) {
						$lastElseIfConditionIsTrue = true;
						break;
					}

					$scope = $scope->filterByFalseyValue($elseif->cond);
				}

				if ($stmt->else === null) {
					$finalScope = $scope->mergeWith($finalScope);
					$alwaysTerminating = false;
				} elseif (!$lastElseIfConditionIsTrue) {
					$branchScopeStatementResult = $this->processStmtNodes($stmt->else->stmts, $scope, $nodeCallback);
					$exitPoints = array_merge($exitPoints, $branchScopeStatementResult->getExitPoints());
					$branchScope = $branchScopeStatementResult->getScope();
					$finalScope = $branchScopeStatementResult->isAlwaysTerminating() ? $finalScope : $branchScope->mergeWith($finalScope);
					$alwaysTerminating = $alwaysTerminating && $branchScopeStatementResult->isAlwaysTerminating();
					if ($branchScopeStatementResult->isAlwaysTerminating()) {
						$alwaysTerminatingStatements = array_merge($alwaysTerminatingStatements, $branchScopeStatementResult->getAlwaysTerminatingStatements());
					}
				}
			}

			if ($finalScope === null) {
				$finalScope = $scope;
			}

			return new StatementResult($finalScope, $alwaysTerminating ? $alwaysTerminatingStatements : [], $exitPoints);
		} elseif ($stmt instanceof Node\Stmt\TraitUse) {
			$this->processTraitUse($stmt, $scope, $nodeCallback);
		} elseif ($stmt instanceof Foreach_) {
			$isIterableAtLeastOnce = $scope->getType($stmt->expr)->isIterableAtLeastOnce()->yes();
			$scope = $this->processExprNode($stmt->expr, $scope, $nodeCallback, 1);
			$bodyScope = $this->enterForeach($scope, $stmt);
			$finalScope = null;
			$count = 0;
			do {
				$prevScope = $bodyScope;
				$bodyScopeResult = $this->processStmtNodes($stmt->stmts, $bodyScope, function (): void {

				})->filterOutLoopTerminationStatements();
				$alwaysTerminating = $bodyScopeResult->isAlwaysTerminating();
				$alwaysTerminatingStatements = $bodyScopeResult->getAlwaysTerminatingStatements();
				$bodyScope = $bodyScopeResult->getScope();
				if (!$isIterableAtLeastOnce || !$this->polluteScopeWithAlwaysIterableForeach) {
					$bodyScope = $bodyScope->mergeWith($scope);
				}
				foreach ($bodyScopeResult->getExitPointsByType(Continue_::class) as $continueExitPoint) {
					$bodyScope = $bodyScope->mergeWith($continueExitPoint->getScope());
				}
				$finalScope = $alwaysTerminating ? $finalScope : $bodyScope->mergeWith($finalScope);
				foreach ($bodyScopeResult->getExitPointsByType(Break_::class) as $breakExitPoint) {
					$finalScope = $breakExitPoint->getScope()->mergeWith($finalScope);
				}
				$bodyScope = $this->enterForeach($bodyScope, $stmt);
				if (!$bodyScope->equals($prevScope)) {
					$bodyScope = $bodyScope->generalizeWith($prevScope);
				} else {
					break;
				}
				$count++;
			} while (!$alwaysTerminating && $count < self::LOOP_SCOPE_ITERATIONS);

			$this->processStmtNodes($stmt->stmts, $bodyScope, $nodeCallback);

			if ($finalScope === null) {
				$finalScope = $scope;
			}

			return new StatementResult($finalScope, $alwaysTerminatingStatements, []);
		} elseif ($stmt instanceof While_) {
			$condBooleanType = $scope->getType($stmt->cond)->toBoolean();
			$isIterableAtLeastOnce = $condBooleanType instanceof ConstantBooleanType && $condBooleanType->getValue();
			$condScope = $this->processExprNode($stmt->cond, $scope, function (): void {

			}, 1);
			if (!$condScope->equals($scope)) {
				$condScope = $condScope->generalizeWith($scope);
			}
			if ($this->polluteScopeWithLoopInitialAssignments) {
				$scope = $condScope;
			}
			$bodyScope = $condScope->filterByTruthyValue($stmt->cond);
			$finalScope = null;
			$count = 0;
			do {
				$prevScope = $bodyScope;
				$bodyScopeResult = $this->processStmtNodes($stmt->stmts, $bodyScope, function (): void {

				})->filterOutLoopTerminationStatements();
				$alwaysTerminating = $bodyScopeResult->isAlwaysTerminating();
				$alwaysTerminatingStatements = $bodyScopeResult->getAlwaysTerminatingStatements();
				$bodyScope = $bodyScopeResult->getScope();
				if (!$isIterableAtLeastOnce) {
					$bodyScope = $bodyScope->mergeWith($scope);
				}
				foreach ($bodyScopeResult->getExitPointsByType(Continue_::class) as $continueExitPoint) {
					$bodyScope = $bodyScope->mergeWith($continueExitPoint->getScope());
				}
				$finalScope = $alwaysTerminating ? $finalScope : $bodyScope->mergeWith($finalScope);
				foreach ($bodyScopeResult->getExitPointsByType(Break_::class) as $breakExitPoint) {
					$finalScope = $breakExitPoint->getScope()->mergeWith($finalScope);
				}
				$bodyScope = $this->processExprNode($stmt->cond, $bodyScope, function (): void {

				}, 1)->filterByTruthyValue($stmt->cond);
				if (!$bodyScope->equals($prevScope)) {
					$bodyScope = $bodyScope->generalizeWith($prevScope);
				} else {
					break;
				}
				$count++;
			} while (!$alwaysTerminating && $count < self::LOOP_SCOPE_ITERATIONS);

			if ($isIterableAtLeastOnce) {
				$bodyScope = $bodyScope->mergeWith($scope);
			}

			$this->processExprNode($stmt->cond, $bodyScope, $nodeCallback, 1);
			$this->processStmtNodes($stmt->stmts, $bodyScope, $nodeCallback);

			if ($finalScope === null) {
				$finalScope = $scope;
			}

			$finalScope = $finalScope->filterByFalseyValue($stmt->cond);

			return new StatementResult($finalScope, $alwaysTerminatingStatements, []);
		} elseif ($stmt instanceof Do_) {
			$finalScope = null;
			$bodyScope = $scope;
			$count = 0;
			do {
				$prevScope = $bodyScope;
				$bodyScopeResult = $this->processStmtNodes($stmt->stmts, $bodyScope, function (): void {

				})->filterOutLoopTerminationStatements();
				$alwaysTerminating = $bodyScopeResult->isAlwaysTerminating();
				$bodyScope = $bodyScopeResult->getScope();
				foreach ($bodyScopeResult->getExitPointsByType(Continue_::class) as $continueExitPoint) {
					$bodyScope = $bodyScope->mergeWith($continueExitPoint->getScope());
				}
				$finalScope = $alwaysTerminating ? $finalScope : $bodyScope->mergeWith($finalScope);
				foreach ($bodyScopeResult->getExitPointsByType(Break_::class) as $breakExitPoint) {
					$finalScope = $breakExitPoint->getScope()->mergeWith($finalScope);
				}
				$bodyScope = $this->processExprNode($stmt->cond, $bodyScope, function (): void {

				}, 1)->filterByTruthyValue($stmt->cond);
				if (!$bodyScope->equals($prevScope)) {
					$bodyScope = $bodyScope->generalizeWith($prevScope);
				} else {
					break;
				}
				$count++;
			} while (!$alwaysTerminating && $count < self::LOOP_SCOPE_ITERATIONS - 1);

			$bodyScope = $bodyScope->mergeWith($scope);

			$bodyScopeResult = $this->processStmtNodes($stmt->stmts, $bodyScope, $nodeCallback)->filterOutLoopTerminationStatements();
			$alwaysTerminating = $bodyScopeResult->isAlwaysTerminating();
			$alwaysTerminatingStatements = $bodyScopeResult->getAlwaysTerminatingStatements();
			$bodyScope = $bodyScopeResult->getScope();
			foreach ($bodyScopeResult->getExitPointsByType(Continue_::class) as $continueExitPoint) {
				$bodyScope = $bodyScope->mergeWith($continueExitPoint->getScope());
			}
			$finalScope = $alwaysTerminating ? $finalScope : $bodyScope->mergeWith($finalScope);
			if (!$alwaysTerminating) {
				$finalScope = $this->processExprNode($stmt->cond, $bodyScope, $nodeCallback, 1)->filterByFalseyValue($stmt->cond);
			}
			foreach ($bodyScopeResult->getExitPointsByType(Break_::class) as $breakExitPoint) {
				$finalScope = $breakExitPoint->getScope()->mergeWith($finalScope);
			}

			return new StatementResult($finalScope, $alwaysTerminatingStatements, []);
		} elseif ($stmt instanceof For_) {
			$initScope = $scope;
			foreach ($stmt->init as $initExpr) {
				$initScope = $this->processExprNode($initExpr, $initScope, $nodeCallback, 0);
			}

			if ($this->polluteScopeWithLoopInitialAssignments) {
				$scope = $initScope;
			}

			$isIterableAtLeastOnce = false; // todo
			$finalScope = null;
			$bodyScope = $initScope;
			foreach ($stmt->cond as $condExpr) {
				$bodyScope = $this->processExprNode($condExpr, $bodyScope, function (): void {

				}, 1)->filterByTruthyValue($condExpr);
			}

			$count = 0;
			do {
				$prevScope = $bodyScope;
				$bodyScopeResult = $this->processStmtNodes($stmt->stmts, $bodyScope, function (): void {

				})->filterOutLoopTerminationStatements();
				$alwaysTerminating = $bodyScopeResult->isAlwaysTerminating();
				$alwaysTerminatingStatements = $bodyScopeResult->getAlwaysTerminatingStatements();
				$bodyScope = $bodyScopeResult->getScope();
				$bodyScope = $bodyScope->mergeWith($scope);
				foreach ($bodyScopeResult->getExitPointsByType(Continue_::class) as $continueExitPoint) {
					$bodyScope = $bodyScope->mergeWith($continueExitPoint->getScope());
				}
				$finalScope = $alwaysTerminating ? $finalScope : $bodyScope->mergeWith($finalScope);
				foreach ($bodyScopeResult->getExitPointsByType(Break_::class) as $breakExitPoint) {
					$finalScope = $breakExitPoint->getScope()->mergeWith($finalScope);
				}
				foreach ($stmt->loop as $loopExpr) {
					$bodyScope = $this->processExprNode($loopExpr, $bodyScope, function (): void {

					}, 0);
				}

				foreach ($stmt->cond as $condExpr) {
					$bodyScope = $this->processExprNode($condExpr, $bodyScope, function (): void {

					}, 1)->filterByTruthyValue($condExpr);
				}

				if (!$bodyScope->equals($prevScope)) {
					$bodyScope = $bodyScope->generalizeWith($prevScope);
				} else {
					break;
				}
				$count++;
			} while (!$alwaysTerminating && $count < self::LOOP_SCOPE_ITERATIONS);

			$originalBodyScope = $bodyScope;
			$bodyScope = $bodyScope->mergeWith($scope);

			foreach ($stmt->cond as $condExpr) {
				$this->processExprNode($condExpr, $bodyScope, $nodeCallback, 1);
			}
			$this->processStmtNodes($stmt->stmts, $bodyScope, $nodeCallback);

			foreach ($stmt->loop as $loopExpr) {
				// todo is $stmt->loop ran when the For_ is dead?
				$this->processExprNode($loopExpr, $originalBodyScope, $nodeCallback, 0);
			}

			if ($finalScope === null) {
				$finalScope = $scope;
			}

			foreach ($stmt->cond as $condExpr) {
				$finalScope = $finalScope->filterByFalseyValue($condExpr);
			}

			return new StatementResult($finalScope, $alwaysTerminatingStatements, []);
		} elseif ($stmt instanceof Switch_) {
			$scope = $this->processExprNode($stmt->cond, $scope, $nodeCallback, 1);
			$finalScope = null;
			$prevScope = null;
			$hasDefaultCase = false;
			foreach ($stmt->cases as $i => $caseNode) {
				if ($caseNode->cond !== null) {
					$condExpr = new BinaryOp\Equal($stmt->cond, $caseNode->cond);
					$branchScope = $this->processExprNode($caseNode->cond, $scope, $nodeCallback, 1);
					$branchScope = $branchScope->filterByTruthyValue($condExpr);
					$scope = $scope->filterByFalseyValue($condExpr);
				} else {
					$hasDefaultCase = true;
					$branchScope = $scope;
					for ($j = $i + 1; $j < count($stmt->cases); $j++) {
						$branchScope = $branchScope->filterByFalseyValue($stmt->cases[$j]->cond);
					}
				}

				$branchScope = $branchScope->mergeWith($prevScope);
				$branchScopeResult = $this->processStmtNodes($caseNode->stmts, $branchScope, $nodeCallback);
				$branchScope = $branchScopeResult->getScope();
				$prevScope = $branchScopeResult->isAlwaysTerminating() ? null : $branchScope;
				$isLastCase = ($i === count($stmt->cases) - 1);
				if ($branchScopeResult->isAlwaysTerminating() || ($isLastCase && !$branchScopeResult->isAlwaysTerminating())) {
					$finalScope = $branchScope->mergeWith($finalScope);
				}

				// todo merge with break and continue
			}

			if (!$hasDefaultCase || $finalScope === null) {
				$finalScope = $scope->mergeWith($finalScope);
			}

			// todo
			// todo StatementResultTest
			return new StatementResult($finalScope, [], []);
		}

		// todo Use_, Global_, Static_, StaticVar_, ClassConst_, Unset_

		return new StatementResult($scope, [], []);
	}

	private function findEarlyTerminatingExpr(Expr $expr, Scope $scope): ?Expr
	{
		if (($expr instanceof MethodCall || $expr instanceof Expr\StaticCall) && count($this->earlyTerminatingMethodCalls) > 0) {
			if ($expr->name instanceof Expr) {
				return null;
			}

			if ($expr instanceof MethodCall) {
				$methodCalledOnType = $scope->getType($expr->var);
			} else {
				if ($expr->class instanceof Name) {
					$methodCalledOnType = $scope->getFunctionType($expr->class, false, false);
				} else {
					$methodCalledOnType = $scope->getType($expr->class);
				}
			}

			$directClassNames = TypeUtils::getDirectClassNames($methodCalledOnType);
			foreach ($directClassNames as $referencedClass) {
				if (!$this->broker->hasClass($referencedClass)) {
					continue;
				}

				$classReflection = $this->broker->getClass($referencedClass);
				foreach (array_merge([$referencedClass], $classReflection->getParentClassesNames()) as $className) {
					if (!isset($this->earlyTerminatingMethodCalls[$className])) {
						continue;
					}

					if (in_array((string) $expr->name, $this->earlyTerminatingMethodCalls[$className], true)) {
						return $expr;
					}
				}
			}
		}

		if ($expr instanceof Exit_) {
			return $expr;
		}

		return null;
	}

	/**
	 * @param \PhpParser\Node\Expr $expr
	 * @param \PHPStan\Analyser\Scope $scope
	 * @param \Closure(\PhpParser\Node $node, Scope $scope): void $nodeCallback
	 * @param int $depth
	 * @return \PHPStan\Analyser\Scope $scope
	 */
	private function processExprNode(Expr $expr, Scope $scope, \Closure $nodeCallback, $depth): Scope
	{
		if ($depth > 0) {
			$scope = $scope->exitFirstLevelStatements();
		}

		$nodeCallback($expr, $scope);

		// todo handle all expr descendants
		if ($expr instanceof Variable) {
			if ($expr->name instanceof Expr) {
				$scope = $this->processExprNode($expr->name, $scope, $nodeCallback, $depth + 1);
			}
		} elseif ($expr instanceof Assign || $expr instanceof AssignRef) {
			$scope = $this->processExprNode($expr->expr, $scope, $nodeCallback, $depth + 1);

			$scope = $this->processAssignVar(
				$scope,
				$expr->var,
				$nodeCallback,
				TrinaryLogic::createYes(),
				$scope->getType($expr->expr)
			);

			if ($expr->var instanceof Variable && is_string($expr->var->name)) {
				$comment = CommentHelper::getDocComment($expr);
				if ($comment !== null) {
					$scope = $this->processVarAnnotation($scope, $expr->var->name, $comment, false);
				}
			}
		} elseif ($expr instanceof Expr\AssignOp) {
			$scope = $this->processExprNode($expr->expr, $scope, $nodeCallback, $depth + 1);
			$scope = $this->processAssignVar(
				$scope,
				$expr->var,
				$nodeCallback,
				TrinaryLogic::createYes(),
				$scope->getType($expr)
			);
		} elseif ($expr instanceof FuncCall) {
			if ($expr->name instanceof Expr) {
				$scope = $this->processExprNode($expr->name, $scope, $nodeCallback, $depth + 1);
			}
			$nodeCallback($expr->name, $scope);
			foreach ($expr->args as $arg) {
				$nodeCallback($arg, $scope);
				$scope = $this->processExprNode($arg->value, $scope, $nodeCallback, $depth + 1);
			}
		} elseif ($expr instanceof MethodCall) {
			$scope = $this->processExprNode($expr->var, $scope, $nodeCallback, $depth + 1);
			if ($expr->name instanceof Expr) {
				$scope = $this->processExprNode($expr->name, $scope, $nodeCallback, $depth + 1);
			}
			foreach ($expr->args as $arg) {
				$nodeCallback($arg, $scope);
				$scope = $this->processExprNode($arg->value, $scope, $nodeCallback, $depth + 1);
			}
		} elseif ($expr instanceof StaticCall) {
			if ($expr->class instanceof Expr) {
				$scope = $this->processExprNode($expr->class, $scope, $nodeCallback, $depth + 1);
			}
			if ($expr->name instanceof Expr) {
				$scope = $this->processExprNode($expr->name, $scope, $nodeCallback, $depth + 1);
			}
			foreach ($expr->args as $arg) {
				$nodeCallback($arg, $scope);
				$scope = $this->processExprNode($arg->value, $scope, $nodeCallback, $depth + 1);
			}
		} elseif ($expr instanceof PropertyFetch) {
			$scope = $this->processExprNode($expr->var, $scope, $nodeCallback, $depth + 1);
			if ($expr->name instanceof Expr) {
				$scope = $this->processExprNode($expr->name, $scope, $nodeCallback, $depth + 1);
			}
		} elseif ($expr instanceof StaticPropertyFetch) {
			if ($expr->class instanceof Expr) {
				$scope = $this->processExprNode($expr->class, $scope, $nodeCallback, $depth + 1);
			}
			if ($expr->name instanceof Expr) {
				$scope = $this->processExprNode($expr->name, $scope, $nodeCallback, $depth + 1);
			}
		} elseif ($expr instanceof Expr\Closure) {
			foreach ($expr->params as $param) {
				$this->processParamNode($param, $scope, $nodeCallback);
			}

			foreach ($expr->uses as $use) {
				$this->processExprNode($use, $scope, $nodeCallback, $depth);
			}

			if ($expr->returnType !== null) {
				$nodeCallback($expr->returnType, $scope);
			}

			$closureScope = $scope->enterAnonymousFunction($expr);
			$this->processStmtNodes($expr->stmts, $closureScope, $nodeCallback);
		} elseif ($expr instanceof Expr\ClosureUse) {
			$this->processExprNode($expr->var, $scope, $nodeCallback, $depth);
		} elseif ($expr instanceof ErrorSuppress) {
			$scope = $this->processExprNode($expr->expr, $scope, $nodeCallback, $depth);
		} elseif ($expr instanceof Exit_) {
			if ($expr->expr !== null) {
				$scope = $this->processExprNode($expr->expr, $scope, $nodeCallback, $depth + 1);
			}
		} elseif ($expr instanceof Node\Scalar\Encapsed) {
			foreach ($expr->parts as $part) {
				$scope = $this->processExprNode($part, $scope, $nodeCallback, $depth + 1);
			}
		} elseif ($expr instanceof ArrayDimFetch) {
			if ($expr->dim !== null) {
				$scope = $this->processExprNode($expr->dim, $scope, $nodeCallback, $depth + 1);
			}

			$scope = $this->processExprNode($expr->var, $scope, $nodeCallback, $depth + 1);
		} elseif ($expr instanceof Array_) {
			// todo isInAssign - like list(), should be handled elsewhere
			foreach ($expr->items as $arrayItem) {
				$scope = $this->processExprNode($arrayItem, $scope, $nodeCallback, $depth + 1);
			}
		} elseif ($expr instanceof ArrayItem) {
			if ($expr->key !== null) {
				$scope = $this->processExprNode($expr->key, $scope, $nodeCallback, $depth + 1);
			}
			$scope = $this->processExprNode($expr->value, $scope, $nodeCallback, $depth + 1);
		} elseif ($expr instanceof BooleanAnd || $expr instanceof BinaryOp\LogicalAnd) {
			$leftScope = $this->processExprNode($expr->left, $scope, $nodeCallback, $depth + 1);
			$rightScope = $this->processExprNode($expr->right, $scope->filterByTruthyValue($expr->left), $nodeCallback, $depth + 1);

			return $leftScope->mergeWith($rightScope);
			// todo nespouštět pravou stranu pokud je levá always false
		} elseif ($expr instanceof BooleanOr || $expr instanceof BinaryOp\LogicalOr) {
			$leftScope = $this->processExprNode($expr->left, $scope, $nodeCallback, $depth + 1);
			$rightScope = $this->processExprNode($expr->right, $scope->filterByFalseyValue($expr->left), $nodeCallback, $depth + 1);
			return $leftScope->mergeWith($rightScope);
			// todo nespouštět pravou stranu pokud je levá always true
		} elseif ($expr instanceof Coalesce) {
			// todo
			$scope = $this->processExprNode($expr->left, $scope, $nodeCallback, $depth + 1);
			$scope = $this->processExprNode($expr->right, $scope, $nodeCallback, $depth + 1);
		} elseif ($expr instanceof BinaryOp) {
			$scope = $this->processExprNode($expr->left, $scope, $nodeCallback, $depth + 1);
			$scope = $this->processExprNode($expr->right, $scope, $nodeCallback, $depth + 1);
		} elseif (
			$expr instanceof Expr\BitwiseNot
			|| $expr instanceof BooleanNot
			|| $expr instanceof Cast
			|| $expr instanceof Expr\Clone_
			|| $expr instanceof Expr\Eval_
			|| $expr instanceof Expr\Include_
			|| $expr instanceof Expr\Print_
			|| $expr instanceof Expr\UnaryMinus
			|| $expr instanceof Expr\UnaryPlus
			|| $expr instanceof Expr\YieldFrom
		) {
			$scope = $this->processExprNode($expr->expr, $scope, $nodeCallback, $depth + 1);
		} elseif ($expr instanceof Expr\ClassConstFetch) {
			if ($expr->class instanceof Expr) {
				$scope = $this->processExprNode($expr->class, $scope, $nodeCallback, $depth + 1);
			}
		} elseif ($expr instanceof Expr\Empty_) {
			// todo
			$scope = $this->processExprNode($expr->expr, $scope, $nodeCallback, $depth + 1);
		} elseif ($expr instanceof Expr\Isset_) {
			// todo
			foreach ($expr->vars as $var) {
				$scope = $this->processExprNode($var, $scope, $nodeCallback, $depth + 1);
			}
		} elseif ($expr instanceof Instanceof_) {
			$scope = $this->processExprNode($expr->expr, $scope, $nodeCallback, $depth + 1);
			if ($expr->class instanceof Expr) {
				$scope = $this->processExprNode($expr->class, $scope, $nodeCallback, $depth + 1);
			}
		} elseif ($expr instanceof List_) {
			// only in assign and foreach, processed elsewhere
			return $scope;
		} elseif ($expr instanceof New_) {
			if ($expr->class instanceof Expr) {
				$scope = $this->processExprNode($expr->class, $scope, $nodeCallback, $depth + 1);
			} elseif ($expr->class instanceof Class_) {
				$this->processStmtNode($expr->class, $scope, $nodeCallback);
			}
		} elseif (
			$expr instanceof Expr\PreInc
			|| $expr instanceof Expr\PostInc
			|| $expr instanceof Expr\PreDec
			|| $expr instanceof Expr\PostDec
		) {
			$scope = $this->processExprNode($expr->var, $scope, $nodeCallback, $depth + 1);
			if (
				$expr->var instanceof Variable
				|| $expr->var instanceof ArrayDimFetch
				|| $expr->var instanceof PropertyFetch
				|| $expr->var instanceof StaticPropertyFetch
			) {
				$expressionType = $scope->getType($expr);
				if ($expressionType instanceof ConstantScalarType) {
					$afterValue = $expressionType->getValue();
					if ($expr instanceof Expr\PostInc) {
						$afterValue++;
					} elseif ($expr instanceof Expr\PostDec) {
						$afterValue--;
					}

					$newExpressionType = $scope->getTypeFromValue($afterValue);
					$scope = $this->processAssignVar(
						$scope,
						$expr->var,
						function (): void {

						},
						TrinaryLogic::createYes(),
						$newExpressionType
					);
				}
			}
		} elseif ($expr instanceof Ternary) {
			$scope = $this->processExprNode($expr->cond, $scope, $nodeCallback, $depth + 1);
			$ifTrueScope = $scope->filterByTruthyValue($expr->cond);
			$ifFalseScope = $scope->filterByFalseyValue($expr->cond);

			if ($expr->if !== null) {
				$ifTrueScope = $this->processExprNode($expr->if, $ifTrueScope, $nodeCallback, $depth + 1);
				$ifFalseScope = $this->processExprNode($expr->if, $ifFalseScope, $nodeCallback, $depth + 1);
			} else {
				$ifFalseScope = $this->processExprNode($expr->else, $ifFalseScope, $nodeCallback, $depth + 1);
			}

			return $ifTrueScope->mergeWith($ifFalseScope);

			// todo do not run else if cond is always true
			// todo do not run if branch if cond is always false
		} elseif ($expr instanceof Expr\Yield_) {
			if ($expr->key !== null) {
				$scope = $this->processExprNode($expr->key, $scope, $nodeCallback, $depth + 1);
			}
			if ($expr->value !== null) {
				$scope = $this->processExprNode($expr->value, $scope, $nodeCallback, $depth + 1);
			}
		}

		if ($depth === 0) {
			$scope = $scope->enterFirstLevelStatements();
		}

		return $scope;
	}

	/**
	 * @param \PhpParser\Node\Param $param
	 * @param \PHPStan\Analyser\Scope $scope
	 * @param \Closure(\PhpParser\Node $node, Scope $scope): void $nodeCallback
	 */
	private function processParamNode(
		Node\Param $param,
		Scope $scope,
		\Closure $nodeCallback
	): void
	{
		if ($param->type !== null) {
			$nodeCallback($param->type, $scope);
		}
		if ($param->default !== null) {
			$this->processExprNode($param->default, $scope, $nodeCallback, 1);
		}
	}

	/**
	 * @param \PHPStan\Analyser\Scope $scope
	 * @param \PhpParser\Node\Expr $var
	 * @param \Closure(\PhpParser\Node $node, Scope $scope): void $nodeCallback
	 * @param TrinaryLogic $certainty
	 * @param Type $subNodeType
	 * @return Scope
	 */
	private function processAssignVar(
		Scope $scope,
		Expr $var,
		\Closure $nodeCallback,
		TrinaryLogic $certainty,
		Type $subNodeType
	): Scope
	{
		$scope = $scope->enterExpressionAssign($var);
		$varScope = $this->processExprNode($var, $scope, $nodeCallback, 1);
		// nepodchytí je ->processExprNode nad voláním ->assignVariable?
		if ($var instanceof Variable && is_string($var->name)) {
			$scope = $scope->assignVariable($var->name, $subNodeType, $certainty);
		} elseif ($var instanceof ArrayDimFetch) {
			$dimExprStack = [];
			while ($var instanceof ArrayDimFetch) {
				$dimExprStack[] = $var->dim;
				$var = $var->var;
			}

			// 1. eval root expr
			$scope = $this->processExprNode($var, $scope, $nodeCallback, 1);

			// 2. eval dimensions
			$offsetTypes = [];
			foreach (array_reverse($dimExprStack) as $dimExpr) {
				if ($dimExpr === null) {
					$offsetTypes[] = null;

				} else {
					if ($dimExpr instanceof Expr\PreInc || $dimExpr instanceof Expr\PreDec) {
						$dimExpr = $dimExpr->var;
					}
					$scope = $this->processExprNode($dimExpr, $scope, $nodeCallback, 1);
					$offsetTypes[] = $scope->getType($dimExpr);
				}
			}

			// 3. eval assigned expr, unfortunately this was already done

			// 4. compose types
			$varType = $scope->getType($var);
			if ($varType instanceof ErrorType) {
				$varType = new ConstantArrayType([], []);
			}
			$offsetValueType = $varType;
			$offsetValueTypeStack = [$offsetValueType];
			foreach (array_slice($offsetTypes, 0, -1) as $offsetType) {
				if ($offsetType === null) {
					$offsetValueType = new ConstantArrayType([], []);

				} else {
					$offsetValueType = $offsetValueType->getOffsetValueType($offsetType);
					if ($offsetValueType instanceof ErrorType) {
						$offsetValueType = new ConstantArrayType([], []);
					}
				}

				$offsetValueTypeStack[] = $offsetValueType;
			}

			$valueToWrite = $subNodeType;
			foreach (array_reverse($offsetTypes) as $offsetType) {
				/** @var Type $offsetValueType */
				$offsetValueType = array_pop($offsetValueTypeStack);
				$valueToWrite = $offsetValueType->setOffsetValueType($offsetType, $valueToWrite);
			}

			if ($var instanceof Variable && is_string($var->name)) {
				$scope = $scope->assignVariable(
					$var->name,
					$valueToWrite,
					$certainty
				);
			} else {
				$scope = $scope->specifyExpressionType(
					$var,
					$valueToWrite
				);
			}
		} elseif ($var instanceof PropertyFetch) {
			$scope = $scope->specifyExpressionType($var, $subNodeType);
		} elseif ($var instanceof Expr\StaticPropertyFetch) {
			$scope = $scope->specifyExpressionType($var, $subNodeType);
		} else {
			$scope = $varScope;
		}

		return $scope;
	}

	private function processVarAnnotation(Scope $scope, string $variableName, string $comment, bool $strict): Scope
	{
		$resolvedPhpDoc = $this->fileTypeMapper->getResolvedPhpDoc(
			$scope->getFile(),
			$scope->isInClass() ? $scope->getClassReflection()->getName() : null,
			$scope->isInTrait() ? $scope->getTraitReflection()->getName() : null,
			$comment
		);
		$varTags = $resolvedPhpDoc->getVarTags();

		if (isset($varTags[$variableName])) {
			$variableType = $varTags[$variableName]->getType();
			return $scope->assignVariable($variableName, $variableType, TrinaryLogic::createYes());

		}

		if (!$strict && count($varTags) === 1 && isset($varTags[0])) {
			$variableType = $varTags[0]->getType();
			return $scope->assignVariable($variableName, $variableType, TrinaryLogic::createYes());

		}

		return $scope;
	}

	private function enterForeach(Scope $scope, Foreach_ $stmt): Scope
	{
		if ($stmt->keyVar !== null && $stmt->keyVar instanceof Variable && is_string($stmt->keyVar->name)) {
			$scope = $scope->assignVariable($stmt->keyVar->name, new MixedType(), TrinaryLogic::createYes());
		}

		$comment = CommentHelper::getDocComment($stmt);
		if ($stmt->valueVar instanceof Variable && is_string($stmt->valueVar->name)) {
			$scope = $scope->enterForeach(
				$stmt->expr,
				$stmt->valueVar->name,
				$stmt->keyVar !== null
				&& $stmt->keyVar instanceof Variable
				&& is_string($stmt->keyVar->name)
					? $stmt->keyVar->name
					: null
			);
			if ($comment !== null) {
				$scope = $this->processVarAnnotation($scope, $stmt->valueVar->name, $comment, true);
			}
		}

		if (
			$stmt->keyVar instanceof Variable && is_string($stmt->keyVar->name)
			&& $comment !== null
		) {
			$scope = $this->processVarAnnotation($scope, $stmt->keyVar->name, $comment, true);
		}

		/*TODO
		 if ($node->valueVar instanceof List_ || $node->valueVar instanceof Array_) {
			$itemTypes = [];
			$exprType = $scope->getType($node->expr);
			$arrayTypes = TypeUtils::getArrays($exprType);
			foreach ($arrayTypes as $arrayType) {
				$itemTypes[] = $arrayType->getItemType();
			}

			$itemType = count($itemTypes) > 0 ? TypeCombinator::union(...$itemTypes) : new MixedType();
			$scope = $this->lookForArrayDestructuringArray($scope, $node->valueVar, $itemType);
		} */

		return $scope;
	}

	private function processTraitUse(Node\Stmt\TraitUse $node, Scope $classScope, \Closure $nodeCallback): void
	{
		foreach ($node->traits as $trait) {
			$traitName = (string) $trait;
			if (!$this->broker->hasClass($traitName)) {
				continue;
			}
			$traitReflection = $this->broker->getClass($traitName);
			$traitFileName = $traitReflection->getFileName();
			if ($traitFileName === false) {
				continue; // trait from eval or from PHP itself
			}
			$fileName = $this->fileHelper->normalizePath($traitFileName);
			if (!isset($this->analysedFiles[$fileName])) {
				continue;
			}
			$parserNodes = $this->parser->parseFile($fileName);
			$this->processNodesForTraitUse($parserNodes, $traitReflection, $classScope, $nodeCallback);
		}
	}

	/**
	 * @param \PhpParser\Node[] $node
	 * @param ClassReflection $traitReflection
	 * @param \PHPStan\Analyser\Scope $scope
	 * @param \Closure(\PhpParser\Node $node): void $nodeCallback
	 */
	private function processNodesForTraitUse($node, ClassReflection $traitReflection, Scope $scope, \Closure $nodeCallback): void
	{
		if ($node instanceof Node) {
			if ($node instanceof Node\Stmt\Trait_ && $traitReflection->getName() === (string) $node->namespacedName) {
				$this->processStmtNodes($node->stmts, $scope->enterTrait($traitReflection), $nodeCallback);
				return;
			}
			if ($node instanceof Node\Stmt\ClassLike) {
				return;
			}
			if ($node instanceof Node\FunctionLike) {
				return;
			}
			foreach ($node->getSubNodeNames() as $subNodeName) {
				$subNode = $node->{$subNodeName};
				$this->processNodesForTraitUse($subNode, $traitReflection, $scope, $nodeCallback);
			}
		} elseif (is_array($node)) {
			foreach ($node as $subNode) {
				$this->processNodesForTraitUse($subNode, $traitReflection, $scope, $nodeCallback);
			}
		}
	}

	/**
	 * @param Scope $scope
	 * @param Node\FunctionLike $functionLike
	 * @return mixed[]
	 */
	private function getPhpDocs(Scope $scope, Node\FunctionLike $functionLike): array
	{
		$phpDocParameterTypes = [];
		$phpDocReturnType = null;
		$phpDocThrowType = null;
		$isDeprecated = false;
		$isInternal = false;
		$isFinal = false;
		$docComment = $functionLike->getDocComment() !== null
			? $functionLike->getDocComment()->getText()
			: null;

		$file = $scope->getFile();
		$class = $scope->isInClass() ? $scope->getClassReflection()->getName() : null;
		$trait = $scope->isInTrait() ? $scope->getTraitReflection()->getName() : null;
		$isExplicitPhpDoc = true;
		if ($functionLike instanceof Node\Stmt\ClassMethod) {
			if (!$scope->isInClass()) {
				throw new \PHPStan\ShouldNotHappenException();
			}
			$phpDocBlock = PhpDocBlock::resolvePhpDocBlockForMethod(
				$this->broker,
				$docComment,
				$scope->getClassReflection()->getName(),
				$trait,
				$functionLike->name->name,
				$file
			);

			if ($phpDocBlock !== null) {
				$docComment = $phpDocBlock->getDocComment();
				$file = $phpDocBlock->getFile();
				$class = $phpDocBlock->getClass();
				$trait = $phpDocBlock->getTrait();
				$isExplicitPhpDoc = $phpDocBlock->isExplicit();
			}
		}

		if ($docComment !== null) {
			$resolvedPhpDoc = $this->fileTypeMapper->getResolvedPhpDoc(
				$file,
				$class,
				$trait,
				$docComment
			);
			$phpDocParameterTypes = array_map(static function (ParamTag $tag): Type {
				return $tag->getType();
			}, $resolvedPhpDoc->getParamTags());
			$nativeReturnType = $scope->getFunctionType($functionLike->getReturnType(), false, false);
			$phpDocReturnType = null;
			if (
				$resolvedPhpDoc->getReturnTag() !== null
				&& (
					$isExplicitPhpDoc
					|| $nativeReturnType->isSuperTypeOf($resolvedPhpDoc->getReturnTag()->getType())->yes()
				)
			) {
				$phpDocReturnType = $resolvedPhpDoc->getReturnTag()->getType();
			}
			$phpDocThrowType = $resolvedPhpDoc->getThrowsTag() !== null ? $resolvedPhpDoc->getThrowsTag()->getType() : null;
			$isDeprecated = $resolvedPhpDoc->isDeprecated();
			$isInternal = $resolvedPhpDoc->isInternal();
			$isFinal = $resolvedPhpDoc->isFinal();
		}

		return [$phpDocParameterTypes, $phpDocReturnType, $phpDocThrowType, $isDeprecated, $isInternal, $isFinal];
	}

}
