<?php

namespace App\StepRunner;

use Illuminate\Support\Facades\DB;

// 此 Runner 的 input table 與 output table 的必須 schema 完全一樣
class SqlOrderBy implements Runner
{
    static function supportedInputStorageType()
    {
        return 'table';
    }

    static function getName()
    {
        return 'SQL 排序';
    }

    static function getFormSchema($bluePrintStorages)
    {
        $inputKeys = [];
        foreach ($bluePrintStorages as $key => $storage) {
            if ($storage['type'] == static::supportedInputStorageType()) {
                $inputKeys[] = $key;
            }
        }

        return [
            'type' => 'object',
            'required' => [
                'name',
                'key',
                'inputs',
                'param'
            ],
            'properties' => [
                'name' => [
                    'type' => 'string',
                    'title' => '步驟名稱'
                ],
                'key' => [
                    'type' => 'string',
                    'title' => '步驟代號'
                ],
                'note' => [
                    'type' => 'string',
                    'title' => '步驟備註'
                ],
                'inputs' => [
                    'type' => 'object',
                    'title' => '選擇輸入資料源',
                    'required' => [
                        'input',
                    ],
                    'properties' => [
                        'input' => [
                            'type' => 'string',
                            'enum' => $inputKeys
                        ]
                    ]
                ],
                'param' => [
                    'type' => 'object',
                    'title' => '步驟參數',
                    'required' => [
                        'order',
                    ],
                    'properties' => [
                        'order' => [
                            'type' => 'array',
                            'items' => [
                                'type' => 'object',
                                'required' => [
                                    'column',
                                    'asc'
                                ],
                                'properties' => [
                                    'column' => [
                                        'type' => 'string',
                                    ],
                                    'asc' => [
                                        'type' => 'boolean'
                                    ]
                                ]
                            ]
                        ]
                    ]
                ],
            ]
        ];
    }

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
        //     'order' => [
        //         [
        //             'column' => 'xxx',
        //             'asc' => true 
        //         ],
        //         [
        //             'column' => 'yyy',
        //             'asc' => false 
        //         ],
        //     ]
        // ]

        $query = "INSERT INTO $outputTable SELECT * FROM $inputTable";
        if (isset($step->param['order'])) {
            $orderBy = collect();
            foreach($step->param['order'] as $s) {
                $column = $s['column'];
                $direct = $s['asc'] ? 'ASC' : 'DESC';
                $orderBy->push("$column $direct");
            }
            $orderBy = $orderBy->implode(',');
            $query = $query . " order by $orderBy";
        }

        DB::statement($query);
    }
}