#!/bin/bash

lake update
lake exe cache get
lake build +Smt:dynlib