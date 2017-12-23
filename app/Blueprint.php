<?php

namespace App;

use Illuminate\Database\Eloquent\Model;
use Illuminate\Support\Facades\DB;


/**
 * App\Blueprint
 *
 * @property int $id
 * @property string $name
 * @property string|null $note
 * @property array $payload
 * @property \Carbon\Carbon|null $created_at
 * @property \Carbon\Carbon|null $updated_at
 * @property-read \Illuminate\Database\Eloquent\Collection|\App\Runtime[] $runtimes
 * @mixin \Eloquent
 */
class Blueprint extends Model
{
    protected $guarded = [];

    protected $casts = [
        'payload' => 'array'
    ];

    public function runtimes()
    {
        return $this->hasMany('App\Runtime');
    }

    /**
     * @return Runtime
     * @throws \Exception
     */
    public function buildRuntime()
    {
        $r = new Runtime;
        $r->blueprint_id = $this->id;
        $r->state = 'init';
        $r->payload = $this->payload;
        $r->save();

        DB::beginTransaction();
        try {
            $r->createRuntimeDatabase();

            $blueprintStorages = $this->payload['storages'];

            $storageMap = [];
            foreach($blueprintStorages as $key => $s) {
                $storageMap[$key] = RuntimeStorage::createStorage($r, $key, $s['type'], $s['name'], $s);
            }

            $blueprintSteps = $this->payload['steps'];
            foreach($blueprintSteps as $key => $s) {
                $inputs = [];
                foreach($s['inputs'] as $type => $k) {
                    $inputs[$type] = $storageMap[$k];
                }

                $output = $storageMap[$s['output']];

                if (!isset($s['note'])) {
                    $s['note'] = '';
                }

                if (!isset($s['param'])) {
                    $s['param'] = [];
                }

                Step::createStep($r, $key, $s['type'], $s['name'], $s['note'], $s['param'], $inputs, $output);
            }
        } catch (\Exception $e) {
            DB::rollback();

            $r->state = 'error';
            $r->error = [
                'message' => $e->getMessage()
            ];
            $r->save();
        }

        return $r;
    }
}
 