<?php

namespace App\StepRunner;

use Illuminate\Support\Facades\DB;

// 此 Runner 的 input table 與 output table 的必須 schema 完全一樣
class SqlLimitOffset extends Runner
{
    static function getBlueprintStepStorage($bluePrintStorages, $bluePrintStepPayload)
    {
        $targetSchema = $bluePrintStorages[$bluePrintStepPayload['inputs']['input']]['schema'];
        return [
            'type' => 'table',
            'schema' => $targetSchema
        ];
    }

    static function run($step)
    {
        $input = $step->connections->first(function($c) {
            return $c->type == 'input';
        });

        $output = $step->connections->first(function($c) {
            return $c->type == 'output';
        });

        $inputTable = $input->storage->payload['table'];
        $outputTable = $output->storage->payload['table'];

        // [
        //     'limit' => 20,
        //     'offset' => 100
        // ]

        $query = "INSERT INTO $outputTable SELECT * FROM $inputTable";
        if (isset($step->param['limit'])) {
            $query = $query . ' limit ' . $step->param['limit'];
        }
        if (isset($step->param['offset'])) {
            $query = $query . ' offset ' . $step->param['offset'];
        }

        DB::statement($query);
    }
}