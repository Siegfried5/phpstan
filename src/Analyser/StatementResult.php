<?php declare(strict_types = 1);

namespace PHPStan\Analyser;

class StatementResult
{

	/** @var Scope */
	private $scope;

	/** @var bool */
	private $alwaysTerminating;

	public function __construct(Scope $scope, bool $alwaysTerminating)
	{
		$this->scope = $scope;
		$this->alwaysTerminating = $alwaysTerminating;
	}

	public function getScope(): Scope
	{
		return $this->scope;
	}

	public function isAlwaysTerminating(): bool
	{
		return $this->alwaysTerminating;
	}

}
