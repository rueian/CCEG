<?php

namespace App\StepRunner;

use Illuminate\Support\Facades\DB;

// 此 Runner 的 output table 的必須 select 完全一樣
class SqlGroupBy extends Runner
{
    static function getBlueprintStepStorage($bluePrintStorages, $bluePrintStepPayload)
    {
        $targetSchema = collect($bluePrintStepPayload['param']['select'])->map(function($select) {
           return [
               'name' => $select['as'],
               'type' => $select['type']
           ];
        });
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
        //     'group' => [
        //         'xxx',
        //         'yyy'
        //     ],
        //     'select' => [
        //         [
        //             'expr' => 'max(xxx)',
        //             'as' => 'max_xxx',
        //             'type' => 'integer',
        //         ],
        //     ]
        // ]

        $outputColumns = collect();
        $selectColumns = collect();

        foreach($step->param['select'] as $column) {
            $outputColumns->push($column['as']);
            $selectColumns->push($column['expr']);
        }

        $outputColumns = $outputColumns->implode(',');
        $selectColumns = $selectColumns->implode(',');

        $groupBy = collect($step->param['group'])->implode(',');

        $query = "INSERT INTO $outputTable ($outputColumns) SELECT $selectColumns FROM $inputTable GROUP BY $groupBy";

        DB::statement($query);
    }
}