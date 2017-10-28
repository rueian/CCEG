<?php

namespace App;

use Illuminate\Database\Eloquent\Model;

class StepConnection extends Model
{
    protected $guarded = [];

    public function step()
    {
        return $this->belongsTo('App\Step');
    }

    public function storage()
    {
        return $this->belongsTo('App\RuntimeStorage', 'runtime_storage_id');
    }
}
