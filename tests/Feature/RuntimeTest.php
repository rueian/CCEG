<?php

namespace Tests\Feature;

use Tests\TestCase;
use Illuminate\Support\Facades\DB;

use App\Blueprint;
use App\Step;
use App\StepConnection;
use App\RuntimeStorage;
use App\Runtime;

class RuntimeTest extends TestCase
{
    public function testStepTopologicalOrdering()
    {
        $b = new Blueprint;
        $b->name = 'blueprint1';
        $b->save();

        $r = new Runtime;
        $r->blueprint_id = $b->id;
        $r->state = 'init';
        $r->save();
        $r->createRuntimeDatabase();

        $s1 = $this->createSimpleStep($r);
        $s2 = $this->createSimpleStep($r);
        $s3 = $this->createSimpleStep($r);
        $s4 = $this->createSimpleStep($r);

        $g1 = $this->createSimpleStorage($r);
        $g2 = $this->createSimpleStorage($r);
        $g3 = $this->createSimpleStorage($r);
        $g4 = $this->createSimpleStorage($r);
        $g5 = $this->createSimpleStorage($r);

        $this->createSimpleConnection($r, $g1, $s3);
        $this->createSimpleConnection($r, $s3, $g2);
        $this->createSimpleConnection($r, $g1, $s2);
        $this->createSimpleConnection($r, $g2, $s2);
        $this->createSimpleConnection($r, $s2, $g3);
        $this->createSimpleConnection($r, $g2, $s4);
        $this->createSimpleConnection($r, $g3, $s4);
        $this->createSimpleConnection($r, $s4, $g4);
        $this->createSimpleConnection($r, $g2, $s1);
        $this->createSimpleConnection($r, $g4, $s1);
        $this->createSimpleConnection($r, $s1, $g5);

        $squence = $r->getStepSequence();

        $this->assertEquals(collect([$s3, $s2, $s4, $s1])->map(function($s) {
            return $s->id;
        }), $squence->map(function($s) {
            return $s->id;
        }));

        $b->delete();
    }

    public function testOneStepRunSQLSelectMap()
    {
        $b = new Blueprint;
        $b->name = 'blueprint1';
        $b->save();

        $r = new Runtime;
        $r->blueprint_id = $b->id;
        $r->state = 'init';
        $r->save();
        $r->createRuntimeDatabase();

        $s1 = RuntimeStorage::createTableStorage($r, 'key1', 'key1',  [
            [
                'name' => 'a',
                'type' => 'integer'
            ],
            [
                'name' => 'b',
                'type' => 'integer'
            ],
        ]);

        $s2 = RuntimeStorage::createTableStorage($r, 'key2', 'key2', [
            [
                'name' => 'a',
                'type' => 'integer'
            ],
            [
                'name' => 'b',
                'type' => 'integer'
            ],
        ]);

        Step::createStep($r, 'key', 'sql_select_map', 'name', 'note', [
            'select' => [
                [ 'expr' => 'a', 'as' => 'b', 'type' => 'integer' ],
                [ 'expr' => 'b', 'as' => 'a', 'type' => 'integer' ],
            ],
        ], [
            'input' => $s1
        ], $s2);

        DB::statement('INSERT INTO ' . $s1->payload['table'] . ' VALUES (1,4), (2,3);');

        $r->runOneStep();

        $t2 = DB::table($s2->payload['table'])->select('a', 'b')->orderBy('b')->get();

        $this->assertEquals((object)['a' => 4, 'b' => 1], $t2[0]);
        $this->assertEquals((object)['a' => 3, 'b' => 2], $t2[1]);

        $r->dropRuntimeDatabase();
        $b->delete();
    }

    public function testOneStepRunSQLOrderBy()
    {
        $b = new Blueprint;
        $b->name = 'blueprint1';
        $b->save();

        $r = new Runtime;
        $r->blueprint_id = $b->id;
        $r->state = 'init';
        $r->save();
        $r->createRuntimeDatabase();

        $s1 = RuntimeStorage::createTableStorage($r, 'key1', 'key1', [
            [
                'name' => 'a',
                'type' => 'integer'
            ],
            [
                'name' => 'b',
                'type' => 'integer'
            ],
        ]);

        $s2 = RuntimeStorage::createTableStorage($r, 'key2', 'key2', [
            [
                'name' => 'a',
                'type' => 'integer'
            ],
            [
                'name' => 'b',
                'type' => 'integer'
            ],
        ]);

        Step::createStep($r, 'key', 'sql_order_by', 'name', 'note', [
            'order' => [
                [
                    'column' => 'a',
                    'direct' => 'asc'
                ],
                [
                    'column' => 'b',
                    'direct' => 'desc'
                ]
            ],
        ], [
            'input' => $s1
        ], $s2);

        DB::statement('INSERT INTO ' . $s1->payload['table'] . ' VALUES (2,3), (1,4), (2, 5);');

        $r->runOneStep();

        $t2 = DB::table($s2->payload['table'])->select('a', 'b')->get();

        $this->assertEquals((object)['a' => 1, 'b' => 4], $t2[0]);
        $this->assertEquals((object)['a' => 2, 'b' => 5], $t2[1]);
        $this->assertEquals((object)['a' => 2, 'b' => 3], $t2[2]);

        $r->dropRuntimeDatabase();
        $b->delete();
    }

    public function testOneStepRunSQLLimitOffset()
    {
        $b = new Blueprint;
        $b->name = 'blueprint1';
        $b->save();

        $r = new Runtime;
        $r->blueprint_id = $b->id;
        $r->state = 'init';
        $r->save();
        $r->createRuntimeDatabase();

        $s1 = RuntimeStorage::createTableStorage($r, 'key1', 'key1', [
            [
                'name' => 'a',
                'type' => 'integer'
            ],
            [
                'name' => 'b',
                'type' => 'integer'
            ],
        ]);

        $s2 = RuntimeStorage::createTableStorage($r, 'key2', 'key2', [
            [
                'name' => 'a',
                'type' => 'integer'
            ],
            [
                'name' => 'b',
                'type' => 'integer'
            ],
        ]);

        Step::createStep($r, 'key', 'sql_limit_offset', 'name', 'note', [
            'limit' => 2,
            'offset' => 2,
        ], [
            'input' => $s1
        ], $s2);

        DB::statement('INSERT INTO ' . $s1->payload['table'] . ' VALUES (2,3), (1,4), (2, 5), (6, 9), (7, 3);');

        $r->runOneStep();

        $t2 = DB::table($s2->payload['table'])->select('a', 'b')->get();

        $this->assertEquals(2, count($t2));
        $this->assertEquals((object)['a' => 2, 'b' => 5], $t2[0]);
        $this->assertEquals((object)['a' => 6, 'b' => 9], $t2[1]);

        $r->dropRuntimeDatabase();
        $b->delete();
    }

    public function testOneStepRunSQLLeftJoin()
    {
        $b = new Blueprint;
        $b->name = 'blueprint1';
        $b->save();

        $r = new Runtime;
        $r->blueprint_id = $b->id;
        $r->state = 'init';
        $r->save();
        $r->createRuntimeDatabase();

        $s1 = RuntimeStorage::createTableStorage($r, 'key1', 'key1', [
            [
                'name' => 'a',
                'type' => 'integer'
            ],
            [
                'name' => 'b',
                'type' => 'integer'
            ],
        ]);

        $s2 = RuntimeStorage::createTableStorage($r, 'key2', 'key2', [
            [
                'name' => 'c',
                'type' => 'integer'
            ],
            [
                'name' => 'd',
                'type' => 'integer'
            ],
        ]);

        $s3 = RuntimeStorage::createTableStorage($r, 'key3', 'key3', [
            [
                'name' => 'key1_a',
                'type' => 'integer'
            ],
            [
                'name' => 'key1_b',
                'type' => 'integer'
            ],
            [
                'name' => 'key2_c',
                'type' => 'integer'
            ],
            [
                'name' => 'key2_d',
                'type' => 'integer'
            ],
        ]);

        Step::createStep($r, 'key', 'sql_left_join', 'name', 'note', [
            'left' => 'b',
            'right' => 'c',
        ], [
            'left' => $s1,
            'right' => $s2,
        ], $s3);

        DB::statement('INSERT INTO ' . $s1->payload['table'] . ' VALUES (2,3), (1,4);');
        DB::statement('INSERT INTO ' . $s2->payload['table'] . ' VALUES (3,8), (4,9);');

        $r->runOneStep();

        $t2 = DB::table($s3->payload['table'])->select('key1_a', 'key1_b', 'key2_c', 'key2_d')->get();

        $this->assertEquals(2, count($t2));
        $this->assertEquals((object)['key1_a' => 2, 'key1_b' => 3, 'key2_c' => 3, 'key2_d' => 8], $t2[0]);
        $this->assertEquals((object)['key1_a' => 1, 'key1_b' => 4, 'key2_c' => 4, 'key2_d' => 9], $t2[1]);

        $r->dropRuntimeDatabase();
        $b->delete();
    }

    public function testOneStepRunSQLFilterBySemiJoin()
    {
        $b = new Blueprint;
        $b->name = 'blueprint1';
        $b->save();

        $r = new Runtime;
        $r->blueprint_id = $b->id;
        $r->state = 'init';
        $r->save();
        $r->createRuntimeDatabase();

        $s1 = RuntimeStorage::createTableStorage($r, 'key1', 'key1', [
            [
                'name' => 'a',
                'type' => 'integer'
            ],
            [
                'name' => 'b',
                'type' => 'integer'
            ],
        ]);

        $s2 = RuntimeStorage::createTableStorage($r, 'key2', 'key2', [
            [
                'name' => 'c',
                'type' => 'integer'
            ],
            [
                'name' => 'd',
                'type' => 'integer'
            ],
        ]);

        $s3 = RuntimeStorage::createTableStorage($r, 'key3', 'key3', [
            [
                'name' => 'a',
                'type' => 'integer'
            ],
            [
                'name' => 'b',
                'type' => 'integer'
            ],
        ]);

        Step::createStep($r, 'key', 'sql_filter_by_semi_join', 'name', 'note', [
            'column' => 'b',
            'operation' => 'in',
            'target' => 'c'
        ], [
            'input' => $s1,
            'semi' => $s2,
        ], $s3);

        DB::statement('INSERT INTO ' . $s1->payload['table'] . ' VALUES (2,3), (1,2), (7,4);');
        DB::statement('INSERT INTO ' . $s2->payload['table'] . ' VALUES (3,8), (4,9);');

        $r->runOneStep();

        $t2 = DB::table($s3->payload['table'])->select('a', 'b')->get();

        $this->assertEquals(2, count($t2));
        $this->assertEquals((object)['a' => 2, 'b' => 3], $t2[0]);
        $this->assertEquals((object)['a' => 7, 'b' => 4], $t2[1]);

        $r->dropRuntimeDatabase();
        $b->delete();
    }

    public function testOneStepRunSQLFilterByCondition()
    {
        $b = new Blueprint;
        $b->name = 'blueprint1';
        $b->save();

        $r = new Runtime;
        $r->blueprint_id = $b->id;
        $r->state = 'init';
        $r->save();
        $r->createRuntimeDatabase();

        $s1 = RuntimeStorage::createTableStorage($r, 'key1', 'key3', [
            [
                'name' => 'a',
                'type' => 'integer'
            ],
            [
                'name' => 'b',
                'type' => 'integer'
            ],
        ]);

        $s2 = RuntimeStorage::createTableStorage($r, 'key2', 'key3', [
            [
                'name' => 'a',
                'type' => 'integer'
            ],
            [
                'name' => 'b',
                'type' => 'integer'
            ],
        ]);

        Step::createStep($r, 'key', 'sql_filter_by_condition', 'name', 'note', [
            'where' => 'a > 5',
        ], [
            'input' => $s1
        ], $s2);

        DB::statement('INSERT INTO ' . $s1->payload['table'] . ' VALUES (2,3), (1,4), (2, 5), (6, 9), (7, 3);');

        $r->runOneStep();

        $t2 = DB::table($s2->payload['table'])->select('a', 'b')->get();

        $this->assertEquals(2, count($t2));
        $this->assertEquals((object)['a' => 6, 'b' => 9], $t2[0]);
        $this->assertEquals((object)['a' => 7, 'b' => 3], $t2[1]);

        $r->dropRuntimeDatabase();
        $b->delete();
    }

    public function testOneStepRunGroupBy()
    {
        $b = new Blueprint;
        $b->name = 'blueprint1';
        $b->save();

        $r = new Runtime;
        $r->blueprint_id = $b->id;
        $r->state = 'init';
        $r->save();
        $r->createRuntimeDatabase();

        $s1 = RuntimeStorage::createTableStorage($r, 'key1', 'key3', [
            [
                'name' => 'a',
                'type' => 'integer'
            ],
            [
                'name' => 'b',
                'type' => 'integer'
            ],
            [
                'name' => 'c',
                'type' => 'integer'
            ],
        ]);

        $s2 = RuntimeStorage::createTableStorage($r, 'key2', 'key3', [
            [
                'name' => 'a',
                'type' => 'integer'
            ],
            [
                'name' => 'b',
                'type' => 'integer'
            ],
            [
                'name' => 'd',
                'type' => 'integer'
            ],
            [
                'name' => 'e',
                'type' => 'integer'
            ],
        ]);

        Step::createStep($r, 'key', 'sql_group_by', 'name', 'note', [
            'group' => [
                'a',
                'b'
            ],
            'select' => [
                [
                    'expr' => 'sum(c)',
                    'as' => 'd',
                    'type' => 'integer'
                ],
                [
                    'expr' => 'b',
                    'as' => 'e',
                    'type' => 'integer'
                ]
            ]
        ], [
            'input' => $s1,
        ], $s2);

        DB::statement('INSERT INTO ' . $s1->payload['table'] . ' VALUES (2,3,4), (2,3,7);');

        $r->runOneStep();

        $t2 = DB::table($s2->payload['table'])->select('d', 'e')->get();

        $this->assertEquals((object)['d' => 11, 'e' => 3], $t2[0]);

        $r->dropRuntimeDatabase();
        $b->delete();
    }

    public function testOneStepRunSmt()
    {
        $b = new Blueprint;
        $b->name = 'blueprint1';
        $b->save();

        $r = new Runtime;
        $r->blueprint_id = $b->id;
        $r->state = 'init';
        $r->save();
        $r->createRuntimeDatabase();

        $smtInput = "
            (declare-const x Int)
            (declare-const y Int)
            (assert (= x 5))
            (assert (= (+ x y) 10))
            (check-sat)
            (get-value (x))
            (get-value (y))
        ";

        $s1 = RuntimeStorage::createSmtInputStorage($r, 'key1', 'key3', $smtInput);
        $s2 = RuntimeStorage::createSmtOutputStorage($r, 'key2', 'key3', '');
        Step::createStep($r, 'key', 'smt', 'name', 'note', [], [
            'input' => $s1
        ], $s2);
        $r->runOneStep();
        $s2->refresh();

        $this->assertEquals(
"sat
((x 5))
((y 5))
", $s2->payload['content']);

        $r->dropRuntimeDatabase();

        $b->delete();
    }

    public function testOneStepRunSmtToTable()
    {
        $b = new Blueprint;
        $b->name = 'blueprint1';
        $b->save();

        $r = new Runtime;
        $r->blueprint_id = $b->id;
        $r->state = 'init';
        $r->save();
        $r->createRuntimeDatabase();

        $smtOutput = "sat
((x 5))
((y 6))
";

        $s1 = RuntimeStorage::createSmtOutputStorage($r, 'key1', 'key3', $smtOutput);
        $s2 = RuntimeStorage::createSmtResultTableStorage($r, 'key3', 'table3');
        Step::createStep($r, 'key', 'smt_output_to_table', 'name', 'note', [], [
            'input' => $s1
        ], $s2);
        $r->runOneStep();

        $t3 = DB::table($s2->payload['table'])->select('variable', 'value')->orderBy('variable')->get();

        $this->assertEquals((object)['variable' => 'x', 'value' => '5'], $t3[0]);
        $this->assertEquals((object)['variable' => 'y', 'value' => '6'], $t3[1]);

        $r->dropRuntimeDatabase();
        $b->delete();
    }

    private function createSimpleStep($r)
    {
        $s = new Step;
        $s->runtime_id = $r->id;
        $s->key = rand() . "key";
        $s->type = 'sql';
        $s->state = 'init';
        $s->save();

        return $s;
    }

    private function createSimpleStorage($r)
    {
        $g = new RuntimeStorage();
        $g->runtime_id = $r->id;
        $g->key = str_random(40);
        $g->type = 'table';
        $g->state = 'init';
        $g->save();

        return $g;
    }

    private function createSimpleConnection($r, $i, $o)
    {
        $n = new StepConnection();
        $n->runtime_id = $r->id;

        if ($i instanceof Step) {
            $n->runtime_storage_id = $o->id;
            $n->step_id = $i->id;
            $n->type = 'output';
        } else {
            $n->runtime_storage_id = $i->id;
            $n->step_id = $o->id;
            $n->type = 'input';
        }

        $n->save();

        return $n;
    }
}
