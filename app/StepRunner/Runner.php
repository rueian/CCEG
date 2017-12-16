<?php

namespace App\StepRunner;

interface Runner
{
    static function run($step);
    static function getBlueprintStepStorage($bluePrintStorages, $bluePrintStepPayload);
    static function supportedInputStorageType();
    static function getName();
    static function getFormSchema($bluePrintStorages);
    static function getFormUISchema();
}