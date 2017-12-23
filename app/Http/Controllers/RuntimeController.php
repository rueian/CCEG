<?php

namespace App\Http\Controllers;

use Illuminate\Http\Request;

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
}
