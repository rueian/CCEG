<?php

namespace App;

use Illuminate\Database\Eloquent\Model;

class RuntimeStorage extends Model
{
    protected $guarded = [];

    public function runtime()
    {
        return $this->belongsTo('App\Runtime');
    }

    public function connections()
    {
        return $this->hasMany('App\StepConnection');
    }
}
