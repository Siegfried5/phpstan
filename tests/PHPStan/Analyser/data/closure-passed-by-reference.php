<?php

namespace ClosurePassedByReference;

function () {

	$progressStarted = false;
	$anotherVariable = false;
	$incrementedInside = 1;
	'beforeCallback';
	$callback = function () use (&$progressStarted, $anotherVariable, &$untouchedPassedByRef, &$incrementedInside): void {
		'inCallbackBeforeAssign';
		if (doFoo()) {
			$progressStarted = 1;
			return;
		}
		if (!$progressStarted) {
			$progressStarted = true;
		}
		if (!$anotherVariable) {
			$anotherVariable = true;
		}

		$incrementedInside++;

		'inCallbackAfterAssign';
	};

	'afterCallback';
};
