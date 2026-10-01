import YesMetaZFC.Model.Forcing.Proper.Elementary.Countable
import YesMetaZFC.SetTheory.CountableDirected
import YesMetaZFC.Model.SetTheory.Internal.MembershipSkolem

/-! # 内部初等模型捕获 club

对 N 中的 club C，C∩N 是非空可数有向族；其并正好是 N∩X。
内部链化把 club 的 ω 链闭性应用到这个实际有向族。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kpair_interpretation_l M (And.left hZFC) (KP.exists_pair (ZF.modelsKP hZF))

/-- N 中的每个实际 club 都包含 N 与其底集的交；所有可数性均在原模型内部。 -/
theorem selem_club_mem_l {ω χ H c T d N S C X K} (hω : M.IsOmega ω)
    (hχ : M.IsRegularCardinal I χ) (hωχ : M.mem ω χ) (hH : H_d I χ H)
    (hM : Smem_d I c H T) (hS : Ssub_d I c d H T N S) (he : Selem_d I ω c d)
    (hωN : M.mem ω N) (hCN : M.mem C N) (hN : M.CardinalLessOrEqual I N ω)
    (hC : Cc_club_d I ω X C) (hK : ∀ x, M.mem x K ↔ M.mem x N ∧ M.mem x X) : M.mem K C := by
  have hHtr := ZF.h_transitive_l I hZF hH
  let L := smdl_structure_l I (R := T) hS.source.2.1
  let Q := smdl_structure_l I (R := S) hS.target.2.1
  let c' : L.Domain := ⟨C, hS.subset C hCN⟩
  have cmem (a : L.Domain) : L.mem a c' ↔ M.mem a.val C := smem_member_l I hS.source hM.2 a c'
  obtain ⟨A, hA⟩ := KP.intersection_exists_d (ZF.modelsKP hZF) C N
  have ha a : M.mem a A ↔ M.mem a C ∧ M.mem a N := hA a
  obtain ⟨F, hF⟩ := ZF.exists_inclusionInjection hZF I (show M.MemberSubset A N from fun a ha' => ((ha a).mp ha').2)
  obtain ⟨G, hG⟩ := hN
  have hAc := ZF.exists_compositionInjection hZF I hF hG
  have hAn : ∃ a, M.mem a A := by
    obtain ⟨E, hE⟩ := KP.exists_empty (ZF.modelsKP hZF)
    obtain ⟨a, haC, _⟩ := hC.unbounded E (fun x hx => (hE x hx).elim)
      (ZF.exists_inclusionInjection hZF I (fun x hx => (hE x hx).elim))
    let φ : UnarySchema 1 := { body := .mem .newest (.bound 1) }
    let ρ : Env L 1 := ⟨fun _ => c', fun _ => c'⟩
    let η : Env Q 1 := ⟨fun _ => ⟨C, hCN⟩, fun _ => ⟨C, hCN⟩⟩
    have hφ (a : L.Domain) : φ.denote ρ a ↔ M.mem a.val C := by
      simpa only [UnarySchema.denote, φ, Formula.satisfies_mem_iff] using! cmem a
    obtain ⟨a', ha'⟩ := selem_witness_l I hZF hω hS he φ ρ η (fun _ => rfl)
      ⟨⟨a, hHtr C c'.property a haC⟩, (hφ _).mpr haC⟩
    exact ⟨a'.val, (ha a'.val).mpr ⟨(hφ _).mp ha', a'.property⟩⟩
  have directed a b (haA : M.mem a A) (hbA : M.mem b A) :
      ∃ v, M.mem v A ∧ M.MemberSubset a v ∧ M.MemberSubset b v := by
    obtain ⟨haC, haN⟩ := (ha a).mp haA
    obtain ⟨hbC, hbN⟩ := (ha b).mp hbA
    obtain ⟨U, hU⟩ := KP.exists_unionOfTwo (ZF.modelsKP hZF) a b
    obtain ⟨v, hvC, hUv⟩ := hC.unbounded U
      (fun x hx => ((hU x).mp hx).elim ((hC.members a haC).1 x) ((hC.members b hbC).1 x))
      (ZF.countable_union_two_l I hZF hω (hC.members a haC).2 (hC.members b hbC).2 hU)
    let ρ : Env L 3 := ((⟨fun _ => c', fun _ => c'⟩ : Env L 1).push ⟨a, hS.subset a haN⟩).push ⟨b, hS.subset b hbN⟩
    let η : Env Q 3 := ((⟨fun _ => ⟨C, hCN⟩, fun _ => ⟨C, hCN⟩⟩ : Env Q 1).push ⟨a, haN⟩).push ⟨b, hbN⟩
    let φ : UnarySchema 3 := {
      body := .conj (.mem .newest (.bound 3))
        (.conj (Formula.subset (.bound 2) .newest) (Formula.subset (.bound 1) .newest)) }
    have hφ (v : L.Domain) : φ.denote ρ v ↔ M.mem v.val C ∧ M.MemberSubset a v.val ∧ M.MemberSubset b v.val := by
      simp only [UnarySchema.denote, φ, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, Formula.satisfies_subset_iff]
      exact and_congr (cmem v) (and_congr (smem_subset_l I hS.source hM.2 hHtr _ v) (smem_subset_l I hS.source hM.2 hHtr _ v))
    obtain ⟨v', hv'⟩ := selem_witness_l I hZF hω hS he φ ρ η (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))
      ⟨⟨v, hHtr C c'.property v hvC⟩, (hφ _).mpr ⟨hvC,
        fun x hx => hUv x ((hU x).mpr (Or.inl hx)), fun x hx => hUv x ((hU x).mpr (Or.inr hx))⟩⟩
    obtain ⟨hv'C, hav, hbv⟩ := (hφ _).mp hv'
    exact ⟨v'.val, (ha v'.val).mpr ⟨hv'C, v'.property⟩, hav, hbv⟩
  have hUnion : M.IsUnionOf K A := by
    intro x
    constructor
    · intro hx
      obtain ⟨hxN, hxX⟩ := (hK x).mp hx
      obtain ⟨E, hE⟩ := KP.exists_empty (ZF.modelsKP hZF)
      obtain ⟨Y, hY⟩ := KP.exists_insert (ZF.modelsKP hZF) E x
      obtain ⟨v, hvC, hYv⟩ := hC.unbounded Y
        (fun y hy => ((hY y).mp hy).elim (fun hy => (hE y hy).elim) (fun hy => hy.symm ▸ hxX))
        (ZF.countable_insert_l I hZF hω (ZF.exists_inclusionInjection hZF I (fun y hy => (hE y hy).elim)) hY)
      let ρ : Env L 2 := (⟨fun _ => c', fun _ => c'⟩ : Env L 1).push ⟨x, hS.subset x hxN⟩
      let η : Env Q 2 := (⟨fun _ => ⟨C, hCN⟩, fun _ => ⟨C, hCN⟩⟩ : Env Q 1).push ⟨x, hxN⟩
      let φ : UnarySchema 2 := { body := .conj (.mem .newest (.bound 2)) (.mem (.bound 1) .newest) }
      have hφ (v : L.Domain) : φ.denote ρ v ↔ M.mem v.val C ∧ M.mem x v.val := by
        simp only [UnarySchema.denote, φ, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff]
        exact and_congr (cmem v) (smem_member_l I hS.source hM.2 ⟨x, hS.subset x hxN⟩ v)
      obtain ⟨v', hv'⟩ := selem_witness_l I hZF hω hS he φ ρ η (Fin.cases rfl (fun _ => rfl))
        ⟨⟨v, hHtr C c'.property v hvC⟩, (hφ _).mpr ⟨hvC, hYv x ((hY x).mpr (Or.inr rfl))⟩⟩
      obtain ⟨hv'C, hxv⟩ := (hφ _).mp hv'
      exact ⟨v'.val, (ha v'.val).mpr ⟨hv'C, v'.property⟩, hxv⟩
    · rintro ⟨v, hv, hxv⟩
      obtain ⟨hvC, hvN⟩ := (ha v).mp hv
      exact (hK x).mpr ⟨selem_countable_subset_l I hM.2 hZFC hω hχ hωχ hH hS he hωN hvN (hC.members v hvC).2 x hxv,
        (hC.members v hvC).1 x hxv⟩
  exact ZFC.cc_club_directed_l I hZFC hω hC (fun a ha' => ((ha a).mp ha').1) hAc hAn directed hUnion

end YesMetaZFC.Model.Forcing.Internal
