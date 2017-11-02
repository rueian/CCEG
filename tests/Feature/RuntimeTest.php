<?php

namespace Tests\Feature;

use Tests\TestCase;
use Illuminate\Foundation\Testing\RefreshDatabase;
use Illuminate\Support\Facades\DB;

use App\Blueprint;
use App\Step;
use App\StepConnection;
use App\RuntimeStorage;
use App\Runtime;

class RuntimeTest extends TestCase
{
    use RefreshDatabase;

    public function testStepTopologicalOrdering()
    {
        $b = new Blueprint;
        $b->name = 'blueprint1';
        $b->save();

        $r = new Runtime;
        $r->blueprint_id = $b->id;
        $r->state = 'init';
        $r->save();

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
        $this->createSimpleConnection($r, $g2, $s2);
        $this->createSimpleConnection($r, $s2, $g3);
        $this->createSimpleConnection($r, $g3, $s4);
        $this->createSimpleConnection($r, $s4, $g4);
        $this->createSimpleConnection($r, $g4, $s1);
        $this->createSimpleConnection($r, $s1, $g5);

        $squence = $r->getStepSequence();

        $this->assertEquals($squence->map(function($s) {
            return $s->id;
        }), collect([$s3, $s2, $s4, $s1])->map(function($s) {
            return $s->id;
        }));
    }

    public function testOneStepRunSQL()
    {
        $b = new Blueprint;
        $b->name = 'blueprint1';
        $b->save();

        $r = new Runtime;
        $r->blueprint_id = $b->id;
        $r->state = 'init';
        $r->save();

        $s1 = RuntimeStorage::createTableStorage($r, 'key1', 'table1', collect([
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
        ]));

        $s2 = RuntimeStorage::createTableStorage($r, 'key2', 'table2', collect([
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
        ]));

        Step::createSQLStep($r, 'step_name', 'step_note', $s1, $s2, [
            'selects' => [
                [ 'select' => 'a', 'rename' => 'b' ],
                [ 'select' => 'b', 'rename' => 'c' ],
                [ 'select' => 'c', 'rename' => 'a' ]
            ],
            'where' => 'a > 1',
            'order' => 'b',
            'limit' => '2'
        ]);

        DB::statement('INSERT INTO table1 VALUES (1,1,0), (2,3,0), (3,2,0), (4,0,6), (5,1,0), (6,5,0);');

        $r->runOneStep();

        $t2 = DB::table('table2')->select('a', 'b', 'c')->orderBy('b')->get();

        $this->assertEquals($t2[0], (object)['a' => 6, 'b' => 4, 'c' => 0]);
        $this->assertEquals($t2[1], (object)['a' => 0, 'b' => 5, 'c' => 1]);
    }

    public function testOneStepRunSMT()
    {
        $b = new Blueprint;
        $b->name = 'blueprint1';
        $b->save();

        $r = new Runtime;
        $r->blueprint_id = $b->id;
        $r->state = 'init';
        $r->save();

        $smtInput = "
            (declare-const x Int)
            (declare-const y Int)
            (assert (= x 5))
            (assert (= (+ x y) 10))
            (check-sat)
            (get-model)
        ";

        $s1 = RuntimeStorage::createSMTInputStorage($r, 'key1', $smtInput);

        $s2 = RuntimeStorage::createSMTOutputStorage($r, 'key2', '');

        Step::createSMTStep($r, 'step_name', 'step_note', $s1, $s2, []);

        $r->runOneStep();

        $s2->refresh();

        $this->assertEquals($s2->payload['content'],
"sat
(model 
  (define-fun y () Int
    5)
  (define-fun x () Int
    5)
)\n"
        );
    }

    private function createSimpleStep($r)
    {
        $s = new Step;
        $s->runtime_id = $r->id;
        $s->type = 'sql';
        $s->state = 'ready';
        $s->save();

        return $s;
    }

    private function createSimpleStorage($r)
    {
        $g = new RuntimeStorage();
        $g->runtime_id = $r->id;
        $g->key = str_random(40);
        $g->type = 'table';
        $g->state = 'ready';
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
