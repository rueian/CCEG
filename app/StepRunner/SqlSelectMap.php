<?php

namespace App\StepRunner;

use Illuminate\Support\Facades\DB;

// 此 Runner 的 output table 的必須 select 完全一樣
class SqlSelectMap implements Runner
{
    static function supportedInputStorageType()
    {
        return 'table';
    }

    static function getName()
    {
        return 'SQL Select 映射';
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
                        'select',
                    ],
                    'properties' => [
                        'select' => [
                            'type' => 'array',
                            'items' => [
                                'type' => 'object',
                                'required' => [
                                    'expr',
                                    'as',
                                    'type'
                                ],
                                'properties' => [
                                    'expr' => [
                                        'type' => 'string'
                                    ],
                                    'as' => [
                                        'type' => 'string'
                                    ],
                                    'type' => [
                                        'type' => 'string',
                                        'enum' => [
                                            'integer',
                                            'float',
                                            'double',
                                            'varchar',
                                        ]
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

        $query = "INSERT INTO $outputTable ($outputColumns) SELECT $selectColumns FROM $inputTable";

        DB::statement($query);
    }
}