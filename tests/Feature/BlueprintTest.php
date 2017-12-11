<?php

namespace Tests\Feature;

use Tests\TestCase;
use App\Blueprint;

class BlueprintTest extends TestCase
{
    public function testBuildRuntime()
    {
        $b = new Blueprint;
        $b->name = 'test';
        $b->payload = [
            'storages' => [
                't1' => [
                    'name' => 'aaa',
                    'type' => 'table',
                    'schema' => [
                        [
                            'name' => 'a',
                            'type' => 'integer'
                        ],
                    ],
                ],
                't2' => [
                    'name' => 'aaa',
                    'type' => 'table',
                    'schema' => [
                        [
                            'name' => 'b',
                            'type' => 'integer'
                        ],
                    ],
                ],
                't3' => [
                    'name' => 'aaa',
                    'type' => 'smt_input',
                    'content' => "
                        (declare-const x Int)
                        (declare-const y Int)
                        (assert (= x 5))
                        (assert (= (+ x y) 10))
                        (check-sat)
                        (get-value (x))
                        (get-value (y))
                    ",
                ],
                't4' => [
                    'name' => 'aaa',
                    'type' => 'smt_output',
                    'content' => '',
                ],
                't5' => [
                    'name' => 'aaa',
                    'type' => 'smt_result',
                ],
            ],
            'steps' => [
                's1' => [
                    'type' => 'sql_select_map',
                    'name' => 'sql_step',
                    'note' => '',
                    'inputs' => [
                        'input' => 't1'
                    ],
                    'output' => 't2',
                    'param' => [
                        'selects' => [
                            [ 'expr' => 'a', 'as' => 'b', 'type' => 'integer' ],
                        ],
                    ],
                ],
                's2' => [
                    'type' => 'smt',
                    'name' => 'smt_step',
                    'note' => '',
                    'inputs' => [
                        'input' => 't3'
                    ],
                    'output' => 't4',
                    'param' => [],
                ],
                's3' => [
                    'type' => 'smt_output_to_table',
                    'name' => 'smt_result_step',
                    'note' => '',
                    'inputs' => [
                        'input' => 't4'
                    ],
                    'output' => 't5',
                    'param' => [],
                ],
            ],
        ];


        $b->save();
        $r = $b->buildRuntime();
        $this->assertEquals(true, $r->exists);

        $r->dropRuntimeDatabase();
        $b->delete();
    }
}
