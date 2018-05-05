<?php

namespace App\Http\Controllers;

use Illuminate\Http\Request;
use Illuminate\Support\Facades\DB;
use App\Runtime;

class RuntimeController extends Controller
{
    public function runOneStep($id)
    {
        $r = Runtime::findOrFail($id);

        try {
            $result = $r->runOneStep();

            if ($result == null) {
                return response()->json([
                    'result' => 'done'
                ]);
            }

            return response()->json([
                'result' => 'success'
            ]);
        } catch(\Exception $e) {
            return response()->json([
                'result' => 'error',
                'error' => $e->getMessage(),
                'refresh' => true
            ], 500);
        }
    }

    public function runToDone($id)
    {
        $r = Runtime::findOrFail($id);

        try {
            $result = true;
            while ($result) {
                $result = $r->runOneStep();
            }

            return response()->json([
                'result' => 'done'
            ]);
        } catch(\Exception $e) {
            return response()->json([
                'result' => 'error',
                'error' => $e->getMessage(),
                'refresh' => true
            ], 500);
        }
    }

    public function resetSteps($id)
    {
        $r = Runtime::findOrFail($id);

        try {
            $r->resetSteps();

            return response()->json([
                'result' => 'done'
            ]);
        } catch (\Exception $e) {
            return response()->json([
                'result' => 'error',
                'error' => $e->getMessage(),
                'refresh' => true
            ], 500);
        }
    }

    public function importInputStorages($id, $fromId)
    {
        $r = Runtime::findOrFail($id);
        $f = Runtime::findOrFail($fromId);

        foreach($f->payload['storages'] as $key => $storage) {
            if (isset($storage['generated']) && $storage['generated']) continue;

            if (isset($r->payload['storages'][$key])) {
                $target = $r->payload['storages'][$key];
                $fields = [];
                foreach($storage['schema'] as $sourceField) {
                    foreach($target['schema'] as $targetField) {
                        if ($sourceField['name'] == $targetField['name'] && $sourceField['type'] == $targetField['type']) {
                            $fields[] = $sourceField;
                        }
                    }
                }
                if (count($fields) == 0) continue;

                $s = $r->storages()->where('key', $key)->firstOrFail();
                $t = $f->storages()->where('key', $key)->firstOrFail();

                DB::beginTransaction();
                try {
                    $s->cleanStorage();

                    $s->import($t->export());

                    $s->state = 'done';
                    $s->save();

                    DB::commit();
                } catch (\Exception $e) {
                    DB::rollback();

                    $s->state = 'error';
                    $s->error = ['message' => $e->getMessage()];
                    $s->save();
                }
            }
        }

        return response()->json([
            'result' => 'done'
        ]);
    }
}
