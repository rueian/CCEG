<?php

namespace App;

use Illuminate\Database\Eloquent\Model;

class Blueprint extends Model
{
    protected $guarded = [];

    public function runtimes()
    {
        return $this->hasMany('App\Runtime');
    }
}
 