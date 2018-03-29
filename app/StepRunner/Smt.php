<?php

namespace App\StepRunner;

use Illuminate\Support\Facades\DB;

class Smt implements Runner
{
    static function supportedInputStorageType()
    {
        return 'smt_variable_table';
    }

    static function getName()
    {
        return 'SMT';
    }

    static function getFormUISchema()
    {
        return [
            'param' => [
                'content' => [
                    'ui:widget' => 'textarea'
                ],
                'varList' => [
                    'items' => [
                        'ui:field' => 'columnCreator'
                    ]
                ],
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
                'inputs'
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
                'param' => [
                    'type' => 'object',
                    'title' => '步驟參數',
                    'properties' => [
                        'varList' => [
                            'title' => '定義變數',
                            'type' => 'array',
                            'items' => [
                                'type' => 'object',
                                'required' => [
                                    'name',
                                    'type'
                                ],
                                'properties' => [
                                    'name' => [
                                        'title' => '變數名稱',
                                        'type' => 'string',
                                    ],
                                    'type' => [
                                        'title' => '變數型別',
                                        'type' => 'string',
                                        'enum' => [
                                            'Int',
                                            'Real',
                                        ],
                                        'enumNames' => [
                                            'Int',
                                            'Real'
                                        ],
                                        'default' => 'Int'
                                    ]
                                ]
                            ]
                        ],
                        'content' => [
                            'type' => 'string',
                            'title' => 'SMT 內容'
                        ],
                    ]
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

    static function getQuotedElemList($line)
    {
        preg_match('/\(([^<]*?)\)/', $line, $matches);
        if (count($matches) > 1) {
            return explode(' ', $matches[1]);
        } else {
            return [];
        }
    }

    static function getBracketsList($line)
    {
        preg_match_all('/\[([^<]*?)\]/', $line, $matches);
        $list = [];
        if (count($matches) > 1) {
            foreach ($matches[1] as $bracket) {
                $list[] = explode(' ', $bracket);
            }
        }
        return $list;
    }

    static function smtExpr($a, $op, $b)
    {
        if ($b == '') {
            return $a;
        }
        return "($op $a $b)";
    }

    // example: macro_declare_int_var_set (a1 a2 a3)
    static function parseMacroDeclareIntVarSet($line)
    {
        $content = '';
        $varList = static::getQuotedElemList($line);
        foreach($varList as $var) {
            $content .= "(declare-const $var Int)\n";
        }
        return $content;
    }

    // example: macro_declare_real_var_set (a1 a2 a3)
    static function parseMacroDeclareRealVarSet($line)
    {
        $content = '';
        $varList = static::getQuotedElemList($line);
        foreach($varList as $var) {
            $content .= "(declare-const $var Real)\n";
        }
        return $content;
    }

    // example: macro_var_set_in_ranges (a1 a2 a3 b1 b2 b3 c1 c2 c3) [10 13] [20 25] [30 35]
    static function parseMacroVarSetInRanges($line)
    {
        $content = '';
        $varList = static::getQuotedElemList($line);
        $rangeList = static::getBracketsList($line);
        foreach($varList as $var) {
            $expr = '';
            foreach ($rangeList as $range) {
                $left = static::smtExpr($var, '>=', $range[0]);
                $right = static::smtExpr($var, '<=', $range[1]);
                $temp = static::smtExpr($left, 'and', $right);
                $expr = static::smtExpr($temp, 'or', $expr);
            }
            $content .= "(assert $expr)\n";
        }
        return $content;
    }

    // example: macro_var_set_mutually_exclusive (a1 a2 a3)
    static function parseMacroVarSetMutuallyExclusive($line)
    {
        $content = '';
        $varList = static::getQuotedElemList($line);
        $length = count($varList);
        for($i = 0; $i < $length; $i++) {
            for ($j = $i + 1; $j < $length; $j++) {
                $varA = $varList[$i];
                $varB = $varList[$j];
                $content .= "(assert (not (= $varA $varB)))\n";
            }
        }
        return $content;
    }

    static function expandSMTMacro($original)
    {
        $content = '';
        $lines = explode("\n", $original);
        foreach($lines as $line) {
            if (starts_with($line, 'macro_declare_int_var_set')) {
                $content .= static::parseMacroDeclareIntVarSet($line) . "\n";
                continue;
            }

            if (starts_with($line, 'macro_declare_real_var_set')) {
                $content .= static::parseMacroDeclareRealVarSet($line) . "\n";
                continue;
            }

            if (starts_with($line, 'macro_var_set_in_ranges')) {
                $content .= static::parseMacroVarSetInRanges($line) . "\n";
                continue;
            }

            if (starts_with($line, 'macro_var_set_mutually_exclusive')) {
                $content .= static::parseMacroVarSetMutuallyExclusive($line) . "\n";
                continue;
            }

            $content .= "$line\n";
        }
        return $content;
    }

    static function getDeclaredConstList($original)
    {
        $list = [];
        $lines = explode("\n", $original);
        foreach ($lines as $line) {
            if (!starts_with($line, '(declare-const ')) {
                continue;
            }
            preg_match('/\(declare-const (.*) (Int|Real)\)/', $line, $matches);
            if (count($matches) > 1) {
                $list[] = $matches[1];
            }
        }
        return $list;
    }

    static function generateSmtInput($varTableName, $stepParam)
    {
        $inputContent = '';

        $VarNameTypeMap = [];
        if (isset($stepParam['varList'])) {
            foreach($stepParam['varList'] as $v) {
                $VarNameTypeMap[$v['name']] = $v['type'];
            }
            foreach($VarNameTypeMap as $name => $type) {
                $inputContent .= "(declare-const $name $type)\n";
            }
        }

        $variables = DB::table($varTableName)->get();
        $VarNameValueMap = [];
        foreach($variables as $v) {
            $VarNameValueMap[$v->variable] = $v->value;
        }
        foreach($VarNameValueMap as $name => $value) {
            if (strlen($value) > 0 && array_key_exists($name, $VarNameTypeMap)) {
                $inputContent .= "(assert (= $name $value))\n";
            }
        }

        $inputContent .= static::expandSMTMacro($stepParam['content']);
        $inputContent .= "(check-sat)\n";

        foreach(static::getDeclaredConstList($inputContent) as $name) {
            $inputContent .= "(get-value ($name))\n";
        }

        return $inputContent;
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
        $param = $step->param;

        $param['input'] = static::generateSmtInput($inputTable, $param);
        $step->param = $param;
        $step->save();

        $descriptorspec = [
            ['pipe', 'r'],  // stdin is a pipe that the child will read from
            ['pipe', 'w'],  // stdout is a pipe that the child will write to
            ['pipe', 'w']   // stderr is a pipe that the child will write to
        ];

        $z3Path = base_path('z3');
        $process = proc_open("$z3Path -smt2 -in 2>&1", $descriptorspec, $pipes, '/tmp', []);
        if (is_resource($process)) {
            fwrite($pipes[0], $param['input']);
            fclose($pipes[0]);

            $out = stream_get_contents($pipes[1]);
            fclose($pipes[1]);
            fclose($pipes[2]);

            $returnValue = proc_close($process);

            $param['output'] = $out;
            $step->param = $param;
            $step->save();

            try {
                if ($returnValue != 0) {
                    throw new \Exception($out);
                } else {
                    // translate SMT (get-value into table row)
                    $lines = explode("\n", trim($out));

                    if (count($lines) > 1) {
                        if ($lines[0] != "sat") {
                            throw new \Exception("smt model is not available");
                        }

                        $outputTable = $output->storage->payload['table'];

                        $query = "INSERT INTO $outputTable (variable, value) VALUES ";

                        $values = [];
                        for($i = 1; $i < count($lines); $i++) {
                            preg_match('/\(\((.*) (.*)\)\)/', $lines[$i], $matches);
                            if (count($matches) == 3) {
                                $k = $matches[1];
                                $v = $matches[2];

                                $values[] = "('$k', $v)";
                            }
                        }
                        $query .= implode(', ', $values);
                        DB::statement($query);
                    }
                }
            } catch (\Exception $err) {
                throw new \Exception($err->getMessage() . "\nSMT input:\n" . $param['input']);
            }
        }
        return;
    }
}