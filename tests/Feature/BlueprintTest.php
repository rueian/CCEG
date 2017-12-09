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
                [
                    'key' => 't1',
                    'type' => 'table',
                    'schema' => [
                        [
                            'name' => 'a',
                            'type' => 'integer'
                        ],
                    ],
                ],
                [
                    'key' => 't2',
                    'type' => 'table',
                    'schema' => [
                        [
                            'name' => 'b',
                            'type' => 'integer'
                        ],
                    ],
                ],
                [
                    'key' => 't3',
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
                [
                    'key' => 't4',
                    'type' => 'smt_output',
                    'content' => '',
                ],
                [
                    'key' => 't5',
                    'type' => 'smt_result',
                ],
            ],
            'steps' => [
                [
                    'type' => 'sql',
                    'name' => 'sql_step',
                    'note' => '',
                    'input' => 't1',
                    'output' => 't2',
                    'param' => [
                        'selects' => [
                            [ 'select' => 'a', 'rename' => 'b' ],
                        ],
                    ],
                ],
                [
                    'type' => 'smt',
                    'name' => 'smt_step',
                    'note' => '',
                    'input' => 't3',
                    'output' => 't4',
                    'param' => [],
                ],
                [
                    'type' => 'smt_output_to_table',
                    'name' => 'smt_result_step',
                    'note' => '',
                    'input' => 't4',
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
