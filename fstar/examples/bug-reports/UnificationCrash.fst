(*
   Copyright 2008-2018 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module UnificationCrash
type tree (a:Type0) = | Tree : a -> tree a
assume val tree_merge : #a:Type -> cmp:(a -> a -> bool) -> h1:tree a -> tree a
#set-options "--debug Crash --debug_level Rel --debug_level RelCheck --debug_level Extreme --debug_level Gen"
let tree_insert cmp h = tree_merge cmp h
