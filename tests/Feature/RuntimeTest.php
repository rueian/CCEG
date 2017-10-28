<?php

namespace Tests\Feature;

use Tests\TestCase;
use Illuminate\Foundation\Testing\RefreshDatabase;
use Illuminate\Support\Facades\DB;

use App\Blueprint;
use App\Step;
use App\RuntimeStorage;
use App\Runtime;

class RuntimeTest extends TestCase
{
    use RefreshDatabase;

    public function testOneStepRun()
    {
        $b = new Blueprint;
        $b->name = 'asdfas';
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
}
