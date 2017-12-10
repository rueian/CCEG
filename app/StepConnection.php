<?php

namespace App;

use Illuminate\Database\Eloquent\Model;

/**
 * App\StepConnection
 *
 * @property int $id
 * @property int $runtime_id
 * @property int $step_id
 * @property int $runtime_storage_id
 * @property string $type
 * @property \Carbon\Carbon|null $created_at
 * @property \Carbon\Carbon|null $updated_at
 * @property-read \App\Step $step
 * @property-read \App\RuntimeStorage $storage
 * @mixin \Eloquent
 */
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
