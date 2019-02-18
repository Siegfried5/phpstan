<?php declare(strict_types = 1);

namespace PHPStan\Analyser;

use PHPStan\Testing\TestCase;
use PHPStan\Type\Constant\ConstantBooleanType;
use PHPStan\Type\Constant\ConstantIntegerType;
use PHPStan\Type\Constant\ConstantStringType;
use PHPStan\Type\ObjectType;
use PHPStan\Type\Type;
use PHPStan\Type\UnionType;
use PHPStan\Type\VerbosityLevel;

class ScopeTest extends TestCase
{

	public function dataGeneralize(): array
	{
		return [
			[
				new ConstantStringType('a'),
				new ConstantStringType('a'),
				'\'a\'',
			],
			[
				new ConstantStringType('a'),
				new ConstantStringType('b'),
				'string',
			],
			[
				new ConstantIntegerType(0),
				new ConstantIntegerType(1),
				'int',
			],
			[
				new UnionType([
					new ConstantIntegerType(0),
					new ConstantIntegerType(1),
				]),
				new UnionType([
					new ConstantIntegerType(0),
					new ConstantIntegerType(1),
					new ConstantIntegerType(2),
				]),
				'int',
			],
			[
				new UnionType([
					new ConstantIntegerType(0),
					new ConstantIntegerType(1),
					new ConstantStringType('foo'),
				]),
				new UnionType([
					new ConstantIntegerType(0),
					new ConstantIntegerType(1),
					new ConstantStringType('foo'),
				]),
				'0|1|\'foo\'',
			],
			[
				new UnionType([
					new ConstantIntegerType(0),
					new ConstantIntegerType(1),
					new ConstantStringType('foo'),
				]),
				new UnionType([
					new ConstantIntegerType(0),
					new ConstantIntegerType(1),
					new ConstantIntegerType(2),
					new ConstantStringType('foo'),
				]),
				'\'foo\'|int',
			],
			[
				new ConstantBooleanType(false),
				new UnionType([
					new ObjectType('Foo'),
					new ConstantBooleanType(false),
				]),
				'Foo|false',
			],
			[
				new UnionType([
					new ObjectType('Foo'),
					new ConstantBooleanType(false),
				]),
				new ConstantBooleanType(false),
				'Foo|false',
			],
			[
				new ObjectType('Foo'),
				new ConstantBooleanType(false),
				'Foo',
			],
		];
	}

	/**
	 * @dataProvider dataGeneralize
	 * @param Type $a
	 * @param Type $b
	 * @param string $expectedTypeDescription
	 */
	public function testGeneralize(Type $a, Type $b, string $expectedTypeDescription): void
	{
		/** @var ScopeFactory $scopeFactory */
		$scopeFactory = $this->getContainer()->getByType(ScopeFactory::class);
		$scopeA = $scopeFactory->create(ScopeContext::create('file.php'))->assignVariable('a', $a);
		$scopeB = $scopeFactory->create(ScopeContext::create('file.php'))->assignVariable('a', $b);
		$resultScope = $scopeA->generalizeWith($scopeB);
		$this->assertSame($expectedTypeDescription, $resultScope->getVariableType('a')->describe(VerbosityLevel::precise()));
	}

}
