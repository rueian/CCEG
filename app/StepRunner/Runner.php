<?php

namespace App\StepRunner;

abstract class Runner
{
    abstract static function run($step);
    abstract static function getBlueprintStepStorage($bluePrintStorages, $bluePrintStepPayload);
}