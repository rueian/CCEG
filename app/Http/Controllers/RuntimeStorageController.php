<?php

namespace App\Http\Controllers;

use App\RuntimeStorage;
use Illuminate\Support\Facades\DB;
use Illuminate\Http\Request;

class RuntimeStorageController extends Controller
{
    /**
     * @param $id
     * @param Request $request
     * @return \Illuminate\Http\JsonResponse
     * @throws \Exception
     */
    public function import($id, Request $request)
    {
        $s = RuntimeStorage::findOrFail($id);

        return $this->doImport($s, $request);
    }

    public function export($id)
    {
        $s = RuntimeStorage::findOrFail($id);

        return $this->doExport($s);
    }

    public function importWithRuntime($id, $key, Request $request)
    {
        $s = RuntimeStorage::where('runtime_id', $id)->where('key', $key)->firstOrFail();

        return $this->doImport($s, $request);
    }

    public function exportWithRuntime($id, $key)
    {
        $s = RuntimeStorage::where('runtime_id', $id)->where('key', $key)->firstOrFail();

        return $this->doExport($s);
    }

    public function doImport(RuntimeStorage $s, Request $request)
    {
        DB::beginTransaction();
        try {
            $s->cleanStorage();

            $s->import($request->input('data'));

            $s->state = 'done';
            $s->save();

            DB::commit();
        } catch (\Exception $e) {
            DB::rollback();

            $s->state = 'error';
            $s->error = ['message' => $e->getMessage()];
            $s->save();

            return response()->json([
                'result' => 'error',
                'error' => $e->getMessage(),
                'refresh' => true
            ], 500);
        }

        return response()->json([
            'result' => 'done'
        ]);
    }

    public function doExport(RuntimeStorage $s)
    {
        return response()->json([
            'type' => $s->type,
            'data' => $s->export()
        ]);
    }
}
