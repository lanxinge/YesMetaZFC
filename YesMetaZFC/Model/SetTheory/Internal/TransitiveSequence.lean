import YesMetaZFC.Model.SetTheory.Internal.TransitiveRecursion
import YesMetaZFC.SetTheory.Ord.Normal

/-! # 传递子源中序数列的绝对性 -/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hKP : M.Models KP) {Z : M.Domain}
  (hZ : M.TransitiveSet Z) (nz : Nonempty {x // M.mem x Z})
  (pair : ∀ a b, M.mem a Z → M.mem b Z → ∃ p, M.mem p Z ∧ Pair_d M p a b)
local notation "N" => rt_model_l Z nz
local notation "I" => kp_pair_l hKP
local notation "J" => rt_pair_l hZ nz (And.left hKP) pair

theorem rt_sequence_l (F n : (N).Domain) :
    (N).IsSequenceOfLength J F n ↔ M.IsSequenceOfLength I F.val n.val :=
  and_congr (rt_ordinal_iff_l hZ nz hKP n)
    (and_congr (rt_function_l hZ nz hKP.1 (KP.exists_pair hKP) pair F)
      (rt_domain_l hKP.1 (KP.exists_pair hKP) hZ nz pair n F))

theorem rt_ordinal_sequence_l (F n : (N).Domain) :
    (N).IsOrdinalValuedSequence J F n ↔ M.IsOrdinalValuedSequence I F.val n.val := by
  refine and_congr (rt_sequence_l hKP hZ nz pair F n) ?_
  constructor
  · intro h i hi x hix
    have ix := rd_entry_transitive_l hZ F.property hix
    exact (rt_ordinal_iff_l hZ nz hKP ⟨x, ix.2⟩).mp
      (h ⟨i, ix.1⟩ hi ⟨x, ix.2⟩ ((rt_entry_l hZ nz hKP.1 ..).mpr hix))
  · intro h i hi x hix
    exact rt_ordinal_l hZ nz x (h i.val hi x.val ((rt_entry_l hZ nz hKP.1 ..).mp hix))

end YesMetaZFC.SetTheory.Internal
