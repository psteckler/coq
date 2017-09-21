(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Generic hash-consing. *)

(** {6 Hashconsing functorial interface} *)

module type HashconsedType =
  sig
    (** {6 Generic hashconsing signature}

        Given an equivalence relation [eq], a hashconsing function is a
        function that associates the same canonical element to two elements
        related by [eq]. Usually, the element chosen is canonical w.r.t.
        physical equality [(==)], so as to reduce memory consumption and
        enhance efficiency of equality tests.

        In order to ensure canonicality, we need a way to remember the element
        associated to a class of equivalence; this is done using the table type
        generated by the [Make] functor.
    *)

    type t
    (** Type of objects to hashcons. *)
    type u
    (** Type of hashcons functions for the sub-structures contained in [t].
        Usually a tuple of functions. *)
    val hashcons :  u -> t -> t
    (** The actual hashconsing function, using its fist argument to recursively
        hashcons substructures. It should be compatible with [eq], that is
        [eq x (hashcons f x) = true]. *)
    val eq : t -> t -> bool
    (** A comparison function. It is allowed to use physical equality
        on the sub-terms hashconsed by the [hashcons] function, but it should be
        insensible to shallow copy of the compared object. *)
    val hash : t -> int
    (** A hash function passed to the underlying hashtable structure. [hash]
        should be compatible with [eq], i.e. if [eq x y = true] then
        [hash x = hash y]. *)
    val use_hashcons : bool
  end

module type S =
  sig
    type t
    (** Type of objects to hashcons. *)
    type u
    (** Type of hashcons functions for the sub-structures contained in [t]. *)
    type table
    (** Type of hashconsing tables *)
    val generate : u -> table
    (** This create a hashtable of the hashconsed objects. *)
    val hcons : table -> t -> t
    (** Perform the hashconsing of the given object within the table. *)
    val stats : table -> Hashset.statistics
    (** Recover statistics of the hashconsing table. *)
  end

module Make (X : HashconsedType) : (S with type t = X.t and type u = X.u)
(** Create a new hashconsing, given canonicalization functions. *)

(** {6 Wrappers} *)

(** These are intended to be used together with instances of the [Make]
    functor. *)

val simple_hcons : ('u -> 'tab) -> ('tab -> 't -> 't) -> 'u -> 't -> 't
(** [simple_hcons f sub obj] creates a new table each time it is applied to any
    sub-hash function [sub]. *)

val recursive_hcons : (('t -> 't) * 'u -> 'tab) -> ('tab -> 't -> 't) -> ('u -> 't -> 't)
(** As [simple_hcons] but intended to be used with well-founded data structures. *)

(** {6 Hashconsing of usual structures} *)

module type HashedType = sig type t val hash : t -> int end

module Hstring : (S with type t = string and type u = unit)
(** Hashconsing of strings.  *)

module Hlist (D:HashedType) :
  (S with type t = D.t list and type u = (D.t list -> D.t list)*(D.t->D.t))
(** Hashconsing of lists.  *)

module Hobj : (S with type t = Obj.t and type u = (Obj.t -> Obj.t) * unit)
(** Hashconsing of OCaml values. *)
