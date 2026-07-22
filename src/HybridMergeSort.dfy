// Copyright (C) 2026 Adam McKellar <dev@mckellar.eu>
// 
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.





module HybridMergeSort {
  import opened Std.Relations

  import opened InsertionSortM

  method {:test} Test() {
    var a: array<int> := new int[][8, 4, 1, 2, 5, 6];
    InsertionSort((x, y) => x <= y, a);
    // assert a[..] == [1, 2, 4, 5, 6, 8];
  }

}


