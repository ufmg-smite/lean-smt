import Smt.Reconstruction.Types
import Smt.Reconstruction.Coe
import Smt.Reconstruction.Term

open Types

open proof
open sort

open Nat

def defaultSEnvironment: SEnvironment := λ _ => ⟨ Nat , default ⟩

def defaultValue (Δ : SEnvironment) (s : sort) : interpSort Δ s :=
  match s with
  | arrow _ s₂ => λ _ => defaultValue Δ s₂
  | atom 0 => Sigma.snd (Δ 0)
  | atom 1 => False
  | atom (succ (succ i)) => Sigma.snd (Δ (succ (succ i)))
  | sort.undef => False
  | sort.array _ _ => False
  | sort.bv _ => False
  | sort.dep => False

def defaultEnvironment: Environment := λ _ Δ s => defaultValue Δ s

