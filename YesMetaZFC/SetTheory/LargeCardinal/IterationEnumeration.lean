import YesMetaZFC.SetTheory.LargeCardinal.IterationAttempt
import YesMetaZFC.SetTheory.LargeCardinal.IterationProjection
import YesMetaZFC.SetTheory.OrdinalChoice

/-! # 从公共可数载体实际编号整列模型

已有单射编号在各模型上反向延拓；缺失编号统一返回该模型的最小编号元素。
最小序数统一化及唯一图替代完成整列构造，只用 ZF，不选择各模型的枚举。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

private def Ja_pick_d (Q ι p n : M.Domain) : Prop := ∃ i k c X R x,
  KPair_d M p i k ∧ Rd_entry_d i c Q ∧ KPair_d M c X R ∧ M.mem x X ∧ Rd_entry_d x n ι ∧
    ∀ y, M.mem y X → Rd_entry_d y k ι → n = k

private def ja_pick_m {d} (Q ι p n : Term d) : Formula 1 d := set[d] ⟪
  ∃ i k c X R x, ⌜kpair_m⌝ₚ(⌜p⌝ₛ, i, k) ∧ ⌜rd_entry0_m⌝ₚ(i, c, ⌜Q⌝ₛ) ∧
    ⌜kpair_m⌝ₚ(c, X, R) ∧ x ∈ X ∧ ⌜rd_entry0_m⌝ₚ(x, ⌜n⌝ₛ, ⌜ι⌝ₛ) ∧
      (∀ y ∈ X, ⌜rd_entry0_m⌝ₚ(y, k, ⌜ι⌝ₛ) → ⌜n⌝ₛ = k)⟫
derive_free_closed ja_pick_m

private theorem ja_pick_sat_l (hE : Extensional M) {d} (ρ : Env M d) (Q ι p n : Term d) :
    Formula.satisfies ρ (ja_pick_m Q ι p n) ↔ Ja_pick_d (Q.eval ρ) (ι.eval ρ) (p.eval ρ) (n.eval ρ) := by
  simp only [ja_pick_m, Ja_pick_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    kpair_sat_l M hE, rd_entry0_sat_l hE, Formula.satisfies_mem_iff, Formula.satisfies_forallMem_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_extensionalEq_iff_eq hE, Definitional.Term.eval_weaken]; rfl

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ja_enum_l {ω α T Q G Z ι : M.Domain} (hω : M.IsOmega ω)
    (h : It_diagram_d hZF ω α T Q G) (inj : M.IsSetInjectionFromTo I ι Z ω)
    (cover : ∀ i c X R, Rd_entry_d i c Q → KPair_d M c X R → M.MemberSubset X Z) :
    ∃ E, Ja_enum_d I ω α Q E := by
  obtain ⟨D, hd⟩ := ZF.exists_cartesianProduct hZF I α ω
  let φ : BinarySchema 2 := { body := ja_pick_m (.bound 2) (.bound 3) (.bound 1) .newest }
  let ρ : Env M 2 := ⟨Fin.cases Q (fun _ => ι), fun _ => ι⟩
  have sat p n : φ.denote ρ p n ↔ Ja_pick_d Q ι p n := ja_pick_sat_l hZF.1 ..
  obtain ⟨u, fu, us⟩ := ZF.ordinal_uniformize_l hZF φ ρ (D := D) (hω.isOrdinal hZF) (by
    intro p hp
    obtain ⟨i, hi, k, _, hp⟩ := (hd p).mp hp
    obtain ⟨c, X, R, hc, mx⟩ := h.model_l hZF hi
    by_cases present : ∃ x, M.mem x X ∧ Rd_entry_d x k ι
    · obtain ⟨x, hx, hxk⟩ := present
      exact ⟨k, (sat p k).mpr ⟨i, k, c, X, R, x, hp, hc, mx.1, hx, hxk, fun _ _ _ => rfl⟩⟩
    · obtain ⟨x, hx⟩ := mx.2.1
      obtain ⟨n, _, hxn⟩ := inj.1.2.2 x (cover i c X R hc mx.1 x hx)
      exact ⟨n, (sat p n).mpr ⟨i, k, c, X, R, x, hp, hc, mx.1, hx, hxn,
        fun y hy hyk => (present ⟨y, hy, hyk⟩).elim⟩⟩) (by
    intro p n _ hn
    obtain ⟨_, _, _, _, _, x, _, _, _, _, hxn, _⟩ := (sat p n).mp hn
    exact inj.1.output_mem_of_pairMember hxn)
  let ψ : BinarySchema 2 := { body := .existsE (.conj (rd_entry0_m (.bound 2) .newest (.bound 3))
    (rd_entry0_m (.bound 1) .newest (.bound 4))) }
  let η : Env M 2 := ⟨Fin.cases u (fun _ => ι), fun _ => ι⟩
  have psat p x : ψ.denote η p x ↔ ∃ n, Rd_entry_d p n u ∧ Rd_entry_d x n ι := by
    simp only [ψ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, rd_entry0_sat_l hZF.1]; rfl
  obtain ⟨r, fr, rs⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I ψ η (source := D) (target := Z) (by
    intro p hp
    obtain ⟨n, _, hpn⟩ := fu.2.1 p hp
    obtain ⟨_, _, _, _, _, x, _, _, _, _, hxn, _⟩ := (sat p n).mp (us p n hpn)
    exact ⟨x, (psat p x).mpr ⟨n, hpn, hxn⟩⟩) (by
    intro p _ x y hx hy
    obtain ⟨n, hpn, hxn⟩ := (psat p x).mp hx
    obtain ⟨m, hpm, hym⟩ := (psat p y).mp hy
    exact inj.2 x y n hxn ((fn0_function_l (ZF.modelsKP hZF) fu).1.2 p m n hpm hpn ▸ hym))
    (fun p x _ hx => ((psat p x).mp hx).elim fun n hn => inj.1.input_mem_of_pairMember hn.2)
  have coordinates p i k (hp : KPair_d M p i k) (hr : ∃ x, Rd_entry_d p x r) : M.mem i α ∧ M.mem k ω := by
    obtain ⟨x, hx⟩ := hr
    obtain ⟨i', hi, k', hk, hp'⟩ := (hd p).mp (fr.input_mem_of_pairMember hx)
    obtain ⟨ei, ek⟩ := kpair_injective_l M hp' hp
    exact ⟨ei ▸ hi, ek ▸ hk⟩
  have typed p i k c X R x (hp : KPair_d M p i k) (hc : Rd_entry_d i c Q) (mx : KPair_d M c X R)
      (hpx : Rd_entry_d p x r) : M.mem x X := by
    obtain ⟨n, hpn, hxn⟩ := (psat p x).mp ((rs p x).mp hpx).2
    obtain ⟨i', k', c', X', R', y, hp', hc', mx', hy, hyn, _⟩ := (sat p n).mp (us p n hpn)
    obtain ⟨ei, ek⟩ := kpair_injective_l M hp' hp
    subst i' k'
    have ec := h.model_function.2 i c' c hc' hc
    subst c'
    obtain ⟨ex, er⟩ := kpair_injective_l M mx' mx
    exact inj.2 y x n hyn hxn ▸ ex ▸ hy
  have onto p i k c X R x (hp : KPair_d M p i k) (hc : Rd_entry_d i c Q) (mx : KPair_d M c X R)
      (hx : M.mem x X) (hxk : Rd_entry_d x k ι) : Rd_entry_d p x r := by
    have hpD := (hd p).mpr ⟨i, (h.model_domain i).mpr ⟨c, hc⟩, k, inj.1.output_mem_of_pairMember hxk, hp⟩
    obtain ⟨n, _, hpn⟩ := fu.2.1 p hpD
    obtain ⟨i', k', c', X', R', y, hp', hc', mx', _, _, pick⟩ := (sat p n).mp (us p n hpn)
    obtain ⟨ei, ek⟩ := kpair_injective_l M hp' hp
    subst i' k'
    have ec := h.model_function.2 i c' c hc' hc
    subst c'
    obtain ⟨ex, er⟩ := kpair_injective_l M mx' mx
    subst X' R'
    exact (rs p x).mpr ⟨hpD, (psat p x).mpr ⟨n, hpn, (pick x hx hxk).symm ▸ hxk⟩⟩
  have row i c X R (hc : Rd_entry_d i c Q) (mx : Smdl_d I c X R) :
      ∃ e, Fn0_d ω X e ∧ It_project_d r i e ∧ ∀ x, M.mem x X → ∃ n, M.mem n ω ∧ Rd_entry_d n x e := by
    let χ : BinarySchema 2 := { body := .existsE (.conj (kpair_m .newest (.bound 3) (.bound 2))
      (rd_entry0_m .newest (.bound 1) (.bound 4))) }
    let δ : Env M 2 := ⟨Fin.cases i (fun _ => r), fun _ => r⟩
    have cs n x : χ.denote δ n x ↔ ∃ p, KPair_d M p i n ∧ Rd_entry_d p x r := by
      simp only [χ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
        kpair_sat_l M hZF.1, rd_entry0_sat_l hZF.1]; rfl
    obtain ⟨e, fe, es⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I χ δ (source := ω) (target := X) (by
      intro n hn
      obtain ⟨p, hp⟩ := (I).total i n
      obtain ⟨x, _, hpx⟩ := fr.2.2 p ((hd p).mpr ⟨i, (h.model_domain i).mpr ⟨c, hc⟩, n, hn, hp⟩)
      exact ⟨x, (cs n x).mpr ⟨p, hp, hpx⟩⟩) (by
      intro n _ x y hx hy
      obtain ⟨p, hp, hpx⟩ := (cs n x).mp hx
      obtain ⟨q, hq, hqy⟩ := (cs n y).mp hy
      exact fr.1.2 p x y hpx (kpair_unique_l M hZF.1 hq hp ▸ hqy))
      (fun n x _ hx => ((cs n x).mp hx).elim fun p hp => typed p i n c X R x hp.1 hc mx.1 hp.2)
    have project : It_project_d r i e := ⟨fe.1.1, fun n x => (es n x).trans
      ⟨fun h => (cs n x).mp h.2, fun ⟨p, hp, hpx⟩ => ⟨(coordinates p i n hp ⟨x, hpx⟩).2, (cs n x).mpr ⟨p, hp, hpx⟩⟩⟩⟩
    refine ⟨e, fn0_of_function_l (ZF.modelsKP hZF) fe, project, fun x hx => ?_⟩
    obtain ⟨n, hn, hxn⟩ := inj.1.2.2 x (cover i c X R hc mx.1 x hx)
    obtain ⟨p, hp⟩ := (I).total i n
    exact ⟨n, hn, (project.2 n x).mpr ⟨p, hp, onto p i n c X R x hp hc mx.1 hx hxn⟩⟩
  obtain ⟨E, ef, ed, es⟩ := it_projects_l hZF (B := α) (r := r) (fun i hi => by
    obtain ⟨c, X, R, hc, mx⟩ := h.model_l hZF hi
    obtain ⟨e, _, ep, _⟩ := row i c X R hc mx
    exact ⟨e, ep⟩)
  refine ⟨E, ef, ed, fun i e c X R he hc hp => ?_⟩
  obtain ⟨X', R', mx⟩ := h.models i c hc
  obtain ⟨ex, er⟩ := kpair_injective_l M mx.1 hp
  subst X' R'
  obtain ⟨f, ff, fp, onto⟩ := row i c X R hc mx
  exact fp.unique_l hZF.1 ((es i e).mp he).2 ▸ ⟨ff, onto⟩

end YesMetaZFC.SetTheory.LargeCardinal
