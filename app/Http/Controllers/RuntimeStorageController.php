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
}
