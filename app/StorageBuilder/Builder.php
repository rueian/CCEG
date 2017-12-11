<?php

namespace App\StorageBuilder;


interface Builder
{
    static function build($runtime, $key, $payload);
}