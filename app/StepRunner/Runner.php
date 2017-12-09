<?php

namespace App\StepRunner;

interface Runner
{
    static function run($step);
    static function getBlueprintStepStorage($bluePrintStorages, $bluePrintStepPayload);
}