<?php

namespace App\StepRunner;

use Illuminate\Support\Facades\DB;

class SmtVariableTableToInput implements Runner
{
    static function run($step)
    {
        $input = $step->connections->first(function($c) {
            return $c->type == 'input';
        });

        $output = $step->connections->first(function($c) {
            return $c->type == 'output';
        });

        $inputTable = $input->storage->payload['table'];

        $variables = DB::table($inputTable)->get();

        $smt = '';
        $list = [];
        foreach($variables as $v) {
            $name = $v->variable;
            $val = $v->value;
            if (strlen($name) > 0) {
                $smt .= "(declare-const $name Real)\n";
                $list[] = $name;
                if (strlen($val) > 0) {
                    $smt .= "(assert (= $name $val))\n";
                }
            }
        }

        $output->storage->payload = [
            'content' => $smt,
            'varList' => $list
        ];
        $output->storage->save();
    }

    static function getBlueprintStepStorage($bluePrintStorages, $bluePrintStepPayload)
    {
        return [
            'type' => 'smt_input',
            'content' => ''
        ];
    }

    static function supportedInputStorageType()
    {
        return 'smt_variable_table';
    }

    static function getName()
    {
        return "變數表格轉換 SMT 輸入";
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
                    'title' => '選擇輸入資料源',
                    'required' => [
                        'input'
                    ],
                    'properties' => [
                        'input' => [
                            'title' => '輸入資料源',
                            'type' => 'string',
                            'enum' => $inputKeys,
                            'enumNames' => $inputNames
                        ]
                    ]
                ],
            ]
        ];
    }

    static function getFormUISchema()
    {
        return [
            'dummy' => []
        ];
    }
}