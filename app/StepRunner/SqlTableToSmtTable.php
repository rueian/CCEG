<?php

namespace App\StepRunner;

use Illuminate\Support\Facades\DB;

class SqlTableToSmtTable implements Runner
{
    static function supportedInputStorageType()
    {
        return 'table';
    }

    static function getName()
    {
        return 'SQL Table to SMT Replace Table';
    }

    static function getFormUISchema()
    {
        return [
            'param' => [
                'variableColumn' => [
                    'ui:widget' => 'columnSelector',
                    'ui:options' => [
                        'inputKey' => 'input'
                    ]
                ],
                'valueColumn' => [
                    'ui:widget' => 'columnSelector',
                    'ui:options' => [
                        'inputKey' => 'input'
                    ]
                ]
            ]
        ];
    }

    static function getFormSchema($bluePrintStorages)
    {
        $inputKeys = [];
        $inputNames = [];
        foreach ($bluePrintStorages as $key => $storage) {
            if ($storage['type'] == static::supportedInputStorageType()) {
                $inputKeys[] = $key;
                $inputNames[] = $storage['name'] . ' (' . $key . ')';
            }
        }

        return [
            'type' => 'object',
            'required' => [
                'name',
                'inputs',
                'param'
            ],
            'properties' => [
                'name' => [
                    'type' => 'string',
                    'title' => '步驟名稱'
                ],
                'note' => [
                    'type' => 'string',
                    'title' => '步驟備註'
                ],
                'inputs' => [
                    'type' => 'object',
                    'title' => '選擇輸入儲存空間',
                    'required' => [
                        'input',
                    ],
                    'properties' => [
                        'input' => [
                            'title' => '輸入儲存空間',
                            'type' => 'string',
                            'enum' => $inputKeys,
                            'enumNames' => $inputNames
                        ]
                    ]
                ],
                'param' => [
                    'type' => 'object',
                    'title' => '步驟參數',
                    'required' => [
                        'variableColumn',
                        'valueColumn'
                    ],
                    'properties' => [
                        'variableColumn' => [
                            'title' => '對應 variable 欄位',
                            'type' => 'string'
                        ],
                        'valueColumn' => [
                            'title' => '對應 value 欄位',
                            'type' => 'string'
                        ]
                    ]
                ],
            ]
        ];
    }

    static function getBlueprintStepStorage($bluePrintStorages, $bluePrintStepPayload)
    {
        return [
            'type' => 'smt_variable_table',
            'schema' => [
                [
                    'name' => 'variable',
                    'type' => 'varchar(255)'
                ],
                [
                    'name' => 'value',
                    'type' => 'varchar(255)'
                ]
            ]
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

        $variableColumn = $step->param['variableColumn'];
        $valueColumn = $step->param['valueColumn'];

        $query = "INSERT INTO $outputTable (variable, value) SELECT $variableColumn, $valueColumn FROM $inputTable";

        DB::statement($query);
    }
}