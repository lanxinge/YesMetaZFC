import YesMetaZFC.SetTheory.Descriptive.RealPair
import YesMetaZFC.SetTheory.Descriptive.Tree

/-! # 有限列的配对解码及子边

长度由图本身唯一决定；定义中的长度量词遍历内部 ω。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Fp_d (ω J r s t : M.Domain) : Prop := ∃ n, M.mem n ω ∧
  M.IsSetFunctionFromTo I s n ω ∧ M.IsSetFunctionFromTo I t n ω ∧ Rp_d I J s t r
def fp_m {d} (ω J r s t : Term d) : Formula 1 d := Formula.existsMem ω (.conj
  (Formula.isFunctionFromTo 𝒞 s.weaken .newest ω.weaken) (.conj
  (Formula.isFunctionFromTo 𝒞 t.weaken .newest ω.weaken) (rp_m (𝒞 := 𝒞) J.weaken s.weaken t.weaken r.weaken)))
derive_free_closed fp_m
theorem fp_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω J r s t : Term d) :
    Formula.satisfies ρ (fp_m (𝒞 := 𝒞) ω J r s t) ↔
      Fp_d I (ω.eval ρ) (J.eval ρ) (r.eval ρ) (s.eval ρ) (t.eval ρ) := by
  simp only [fp_m, Fp_d, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_isFunctionFromTo_iff I hE, rp_sat_l I, Definitional.Term.eval_weaken]; rfl

theorem fp_unique_l (hE : Extensional M) {ω J r s t u v} (hJ : Npair_d I ω J)
    (h : Fp_d I ω J r s t) (k : Fp_d I ω J r u v) : s = u ∧ t = v := by
  obtain ⟨_, _, hs, ht, hp⟩ := h
  obtain ⟨_, _, hu, hv, hq⟩ := k
  have a := (rp_subset_l I hJ hs ht hp hq).mp (fun _ => id)
  have b := (rp_subset_l I hJ hu hv hq hp).mp (fun _ => id)
  exact ⟨hE.eq_of_same_members s u (fun p => ⟨a.1 p, b.1 p⟩),
    hE.eq_of_same_members t v (fun p => ⟨a.2 p, b.2 p⟩)⟩

theorem fp_type_l (hZF : M.Models ZF) {ω A J r s t} (hA : Fseq_space_d I ω ω A)
    (hJ : Npair_d I ω J) (h : Fp_d I ω J r s t) : M.mem r A ∧ M.mem s A ∧ M.mem t A := by
  obtain ⟨n, hn, hs, ht, hp⟩ := h
  exact ⟨(hA r).mpr ⟨n, hn, rp_type_l I hZF hJ hs ht hp⟩, (hA s).mpr ⟨n, hn, hs⟩, (hA t).mpr ⟨n, hn, ht⟩⟩

theorem fp_decode_l (hZF : M.Models ZF) {ω A J r} (hA : Fseq_space_d I ω ω A)
    (hJ : Npair_d I ω J) (hr : M.mem r A) : ∃ s t, Fp_d I ω J r s t := by
  obtain ⟨n, hn, hr⟩ := (hA r).mp hr
  obtain ⟨s, t, hs, ht, hp⟩ := rp_decode_l I hZF hJ hr
  exact ⟨s, t, n, hn, hs, ht, hp⟩

theorem fp_at_l (hZF : M.Models ZF) {ω J r s t D} (hJ : Npair_d I ω J)
    (h : Fp_d I ω J r s t) (hr : M.IsSetFunctionFromTo I r D ω) :
    M.IsSetFunctionFromTo I s D ω ∧ M.IsSetFunctionFromTo I t D ω ∧ Rp_d I J s t r := by
  obtain ⟨n, _, hs, ht, hp⟩ := h
  have e := hZF.1.eq_of_same_members n D (fun i => ((rp_type_l I hZF hJ hs ht hp).2.1 i).trans (hr.2.1 i).symm)
  exact ⟨e ▸ hs, e ▸ ht, hp⟩

theorem fp_sub_l {ω J r s t q u v} (hJ : Npair_d I ω J)
    (h : Fp_d I ω J r s t) (k : Fp_d I ω J q u v) :
    M.MemberSubset r q ↔ M.MemberSubset s u ∧ M.MemberSubset t v := by
  obtain ⟨_, _, hs, ht, hp⟩ := h
  obtain ⟨_, _, _, _, hq⟩ := k
  exact rp_subset_l I hJ hs ht hp hq

theorem fp_step_l (hZF : M.Models ZF) {ω J r s t q u v} (hω : M.IsOmega ω) (hJ : Npair_d I ω J)
    (h : Fp_d I ω J r s t) (k : Fp_d I ω J q u v) :
    Step_d I ω r q ↔ Step_d I ω s u ∧ Step_d I ω t v := by
  obtain ⟨n, hn, hs, ht, hp⟩ := h
  obtain ⟨m, hm, hu, hv, hq⟩ := k
  rw [tree_step_iff_l I hZF hω hn hm (rp_type_l I hZF hJ hs ht hp) (rp_type_l I hZF hJ hu hv hq),
    tree_step_iff_l I hZF hω hn hm hs hu, tree_step_iff_l I hZF hω hn hm ht hv, rp_subset_l I hJ hs ht hp hq]
  exact ⟨fun h => ⟨⟨h.1, h.2.1⟩, h.1, h.2.2⟩, fun h => ⟨h.1.1, h.1.2, h.2.2⟩⟩

/-- 同步延伸两个分量所得的配对仍是一个子节点。 -/
theorem fp_child_l (hZF : M.Models ZF) {ω A J r s t u v} (hω : M.IsOmega ω)
    (hA : Fseq_space_d I ω ω A) (hJ : Npair_d I ω J) (h : Fp_d I ω J r s t)
    (hu : M.mem u A) (hv : M.mem v A) (hsu : Step_d I ω s u) (htv : Step_d I ω t v) :
    ∃ q, Fp_d I ω J q u v ∧ Step_d I ω r q := by
  obtain ⟨n, hn, hs, ht, _⟩ := h
  obtain ⟨m, hm, hu⟩ := (hA u).mp hu
  obtain ⟨l, hl, hv⟩ := (hA v).mp hv
  have sm := ((tree_step_iff_l I hZF hω hn hm hs hu).mp hsu).1
  have sl := ((tree_step_iff_l I hZF hω hn hl ht hv).mp htv).1
  have e := hZF.1.eq_of_same_members l m (fun x => (sl x).trans (sm x).symm)
  subst l
  obtain ⟨q, _, hq⟩ := rp_exists_l I hZF hJ hu hv
  have hp : Fp_d I ω J q u v := ⟨m, hm, hu, hv, hq⟩
  exact ⟨q, hp, (fp_step_l I hZF hω hJ ⟨n, hn, hs, ht, ‹Rp_d I J s t r›⟩ hp).mpr ⟨hsu, htv⟩⟩

end YesMetaZFC.SetTheory.Descriptive
