<?php

namespace App;

use App\StorageBuilder\SmtInputStorageBuilder;
use App\StorageBuilder\SmtOutputStorageBuilder;
use App\StorageBuilder\SmtResultTableStorageBuilder;
use App\StorageBuilder\TableStorageBuilder;
use Illuminate\Database\Eloquent\Model;

/**
 * App\RuntimeStorage
 *
 * @property int $id
 * @property int $runtime_id
 * @property string $key
 * @property string $type
 * @property array $payload
 * @property string $state
 * @property mixed|null $error
 * @property \Carbon\Carbon|null $created_at
 * @property \Carbon\Carbon|null $updated_at
 * @property-read \Illuminate\Database\Eloquent\Collection|\App\StepConnection[] $connections
 * @property-read \App\Runtime $runtime
 * @mixin \Eloquent
 */
class RuntimeStorage extends Model
{
    public static $builderMap = [
        'table' => TableStorageBuilder::class,
        'smt_input' => SmtInputStorageBuilder::class,
        'smt_output' => SmtOutputStorageBuilder::class,
        'smt_result' => SmtResultTableStorageBuilder::class
    ];

    protected $guarded = [];

    protected $casts = [
        'payload' => 'array'
    ];

    public function runtime()
    {
        return $this->belongsTo('App\Runtime');
    }

    public function connections()
    {
        return $this->hasMany('App\StepConnection');
    }


    /**
     * @param $runtime
     * @param $key
     * @param $type
     * @param $payload
     * @return RuntimeStorage
     * @throws \Exception
     */
    static public function createStorage($runtime, $key, $type, $payload)
    {
        $builder = static::$builderMap[$type];
        if (!$builder) {
            throw new \Exception('Un supported storage type: '.$type);
        }

        return $builder::build($runtime, $key, $payload);
    }

    static public function createSmtInputStorage($runtime, $key, $content)
    {
        return SmtInputStorageBuilder::build($runtime, $key, [
            'content' => $content
        ]);
    }

    static public function createSmtOutputStorage($runtime, $key, $content)
    {
        return SmtOutputStorageBuilder::build($runtime, $key, [
            'content' => $content
        ]);
    }

    static public function createTableStorage($runtime, $key, $schema)
    {
        return TableStorageBuilder::build($runtime, $key, [
            'schema' => $schema
        ]);
    }

    static public function createSmtResultTableStorage($runtime, $key)
    {
        return SmtResultTableStorageBuilder::build($runtime, $key, []);
    }
}
