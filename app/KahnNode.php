<?php

namespace App;

class KahnNode
{
    public $v;
    public $refCount;
    public $adjList;

    public function __construct(&$v) {
        $this->v = $v;
        $this->refCount = 0;
        $this->adjList = collect();
    }
}