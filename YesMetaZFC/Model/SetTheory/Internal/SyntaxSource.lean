import YesMetaZFC.Model.SetTheory.Reflection.TransitiveSequence
import YesMetaZFC.Model.SetTheory.Types.FlatSatisfaction
import YesMetaZFC.Model.SetTheory.Internal.Theory

/-! # 原有 Kuratowski 程序在传递子源中的语法绝对性 -/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {Z : M.Domain}

section Pairing
variable (hE : Extensional M) (hP : ∀ a b : M.Domain, ∃ p, Pair_d M p a b)
  (hZ : M.TransitiveSet Z) (nz : Nonempty {x // M.mem x Z})
  (pair : ∀ a b, M.mem a Z → M.mem b Z → ∃ p, M.mem p Z ∧ Pair_d M p a b)
local notation "N" => rt_model_l Z nz
local notation "I" => kpair_interpretation_l M hE hP
local notation "J" => rt_pair_l hZ nz hE pair

theorem rt_sop_l (k : Nat) (c i j : (N).Domain) :
    Sop_d J k c i j ↔ Sop_d I k c.val i.val j.val := by
  have code := rt_kpair_l hE hP hZ nz pair
  constructor
  · rintro ⟨a, o, ho, ha, hc⟩
    exact ⟨a.val, o.val, (rt_num_l hZ nz hE k o).mp ho, (code ..).mp ha, (code ..).mp hc⟩
  · rintro ⟨a, o, ho, ha, hc⟩
    have oa := hc.mem_l M hZ c.property
    exact ⟨⟨a, oa.2⟩, ⟨o, oa.1⟩, (rt_num_l hZ nz hE k _).mpr ho, (code ..).mpr ha, (code ..).mpr hc⟩

theorem rt_sfm_node_l (ω r c : (N).Domain) :
    Sfm_node_d J ω r c ↔ Sfm_node_d I ω.val r.val c.val := by
  have step (k : Nat) (A B : (N).Domain) :
      (∃ i j, Sop_d J k c i j ∧ (N).mem i A ∧ (N).mem j B) ↔
        ∃ i j, Sop_d I k c.val i j ∧ M.mem i A.val ∧ M.mem j B.val := by
    constructor
    · rintro ⟨i, j, hs, hi, hj⟩
      exact ⟨i.val, j.val, (rt_sop_l hE hP hZ nz pair ..).mp hs, hi, hj⟩
    · rintro ⟨i, j, hs, hi, hj⟩
      exact ⟨⟨i, hZ A.val A.property i hi⟩, ⟨j, hZ B.val B.property j hj⟩,
        (rt_sop_l hE hP hZ nz pair ..).mpr hs, hi, hj⟩
  exact or_congr (step 0 ω ω) (or_congr (step 1 ω ω) (or_congr (step 2 r r) (step 3 ω r)))
end Pairing

variable (hKP : M.Models KP) (hZ : M.TransitiveSet Z) (nz : Nonempty {x // M.mem x Z})
  (pair : ∀ a b, M.mem a Z → M.mem b Z → ∃ p, M.mem p Z ∧ Pair_d M p a b)
local notation "N" => rt_model_l Z nz
local notation "I" => kp_pair_l hKP
local notation "J" => rt_pair_l hZ nz (And.left hKP) pair

theorem rt_sfm_l (ω n F : (N).Domain) : Sfm_d J ω n F ↔ Sfm_d I ω.val n.val F.val := by
  refine and_congr Iff.rfl (and_congr (rt_sequence_l hKP hZ nz pair F n) ?_)
  constructor
  · intro h r c hrc
    have rc := rd_entry_transitive_l hZ F.property hrc
    exact (rt_sfm_node_l hKP.1 (KP.exists_pair hKP) hZ nz pair ..).mp
      (h ⟨r, rc.1⟩ ⟨c, rc.2⟩ ((rt_entry_l hZ nz hKP.1 ..).mpr hrc))
  · intro h r c hrc
    exact (rt_sfm_node_l hKP.1 (KP.exists_pair hKP) hZ nz pair ..).mpr
      (h r.val c.val ((rt_entry_l hZ nz hKP.1 ..).mp hrc))

theorem rt_sformula_l (ω a n F k : (N).Domain) :
    Sformula_d J ω a n F k ↔ Sformula_d I ω.val a.val n.val F.val k.val :=
  and_congr (rt_kpair_l hKP.1 (KP.exists_pair hKP) hZ nz pair a F k)
    (and_congr (rt_sfm_l hKP hZ nz pair ω n F) Iff.rfl)

end YesMetaZFC.SetTheory.Internal
