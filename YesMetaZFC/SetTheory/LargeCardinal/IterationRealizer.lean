import YesMetaZFC.SetTheory.LargeCardinal.IterationWellFounded
import YesMetaZFC.SetTheory.LargeCardinal.IterationCofinal

/-! # 由实际相容实现证明树枝良基

每条腿是已编码的集合函数，只要求保持成员关系并与树嵌入交换。
不要求它满射、单射或初等。将整列腿装配成带标号载体上的映射，
直接极限的泛性质把良基目标上的最小元性质回拉到商。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

structure It_realizer_d (hZF : M.Models ZF) (B Q G Y V P : M.Domain) : Prop where
  function : M.IsSetFunction (kp_pair_l (ZF.modelsKP hZF)) P
  domain : M.IsDomainOf (kp_pair_l (ZF.modelsKP hZF)) B P
  maps : ∀ i f c X R, Rd_entry_d i f P → Rd_entry_d i c Q → Smdl_d (kp_pair_l (ZF.modelsKP hZF)) c X R →
    Fn0_d X Y f ∧ ∀ x y u v, Rd_entry_d x u f → Rd_entry_d y v f → Rd_entry_d x y R → Rd_entry_d u v V
  commute : ∀ i j f u v, It_map_d G i j f → Rd_entry_d i u P → Rd_entry_d j v P →
    ∀ x y z, Rd_entry_d x y f → Rd_entry_d y z v → Rd_entry_d x z u

def It_value_d (P a y : M.Domain) : Prop := ∃ i x f, KPair_d M a i x ∧ Rd_entry_d i f P ∧ Rd_entry_d x y f
def it_value_m {d} (P a y : Term d) : Formula 1 d := .existsE (.existsE (.existsE
  (.conj (kpair_m a.weaken.weaken.weaken (.bound 2) (.bound 1))
    (.conj (rd_entry_m (.bound 2) .newest P.weaken.weaken.weaken) (rd_entry_m (.bound 1) y.weaken.weaken.weaken .newest)))))
derive_free_closed it_value_m

theorem it_value_sat_l (hE : Extensional M) {d} (ρ : Env M d) (P a y : Term d) :
    Formula.satisfies ρ (it_value_m P a y) ↔ It_value_d (P.eval ρ) (a.eval ρ) (y.eval ρ) := by
  simp only [it_value_m, It_value_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    kpair_sat_l M hE, rd_entry_sat_l hE, Definitional.Term.eval_weaken]; rfl

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem It_cone_d.realizer_l {ω B Q G d Y V P : M.Domain} (hω : M.IsOmega ω)
    (h : It_cone_d hZF ω B Q G d Y V P) : It_realizer_d hZF B Q G Y V P :=
  ⟨h.function, h.domain, fun i f c X R hf hc mx =>
    ⟨fn0_of_function_l (ZF.modelsKP hZF) (h.elementary i f c X R hf hc mx).1.1,
      fun _ _ _ _ hx hy hr => ((h.elementary i f c X R hf hc mx).relation_l I hZF hω mx h.model hx hy).mp hr⟩,
    h.commute⟩

theorem It_realizer_d.restrict_l {B D Q G Y V P : M.Domain} (h : It_realizer_d hZF B Q G Y V P)
    (sub : M.MemberSubset D B) : ∃ P', It_realizer_d hZF D Q G Y V P' ∧
      ∀ i f, Rd_entry_d i f P' ↔ M.mem i D ∧ Rd_entry_d i f P := by
  obtain ⟨P', hp⟩ := ZF.exists_restriction hZF I P D
  refine ⟨P', ⟨hp.isSetFunction h.function, ?_, fun i f c X R hi hc mx => h.maps i f c X R ((hp.2 i f).mp hi).2 hc mx,
    fun i j f u v hf hu hv => h.commute i j f u v hf ((hp.2 i u).mp hu).2 ((hp.2 j v).mp hv).2⟩, hp.2⟩
  intro i
  exact ⟨fun hi => by
    obtain ⟨f, hf⟩ := (h.domain i).mp (sub i hi)
    exact ⟨f, (hp.2 i f).mpr ⟨hi, hf⟩⟩, fun ⟨f, hf⟩ => ((hp.2 i f).mp hf).1⟩

theorem it_realizer_wf_l {ω α T Q G B L A p H R q C S Y V P : M.Domain}
    (h : It_diagram_d hZF ω α T Q G) (inside : M.MemberSubset B α) (s : It_system_d B L Q G A p H R)
    (limit : Di_limit_d A p H R q C S) (realizer : It_realizer_d hZF B Q G Y V P) (wf : Wf_rel_d Y V) : Wf_rel_d C S := by
  obtain ⟨D, hq⟩ := h.family_l hZF
  have map i f (hf : Rd_entry_d i f P) : ∃ c X R, Rd_entry_d i c Q ∧ Smdl_d I c X R ∧ Fn0_d X Y f := by
    obtain ⟨c, X, R, hc, mx⟩ := h.model_l hZF (inside i ((realizer.domain i).mpr ⟨f, hf⟩))
    exact ⟨c, X, R, hc, mx, (realizer.maps i f c X R hf hc mx).1⟩
  let φ : BinarySchema 1 := { body := it_value_m (.bound 2) (.bound 1) .newest }
  let ρ : Env M 1 := ⟨fun _ => P, fun _ => P⟩
  have sat a y : φ.denote ρ a y ↔ It_value_d P a y := it_value_sat_l hZF.1 ..
  obtain ⟨r, hr, rs⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := A) (target := Y)
    (fun a ha => by
      obtain ⟨i, x, hi, hp, hx⟩ := (s.tags.nodes a).mp ha
      obtain ⟨f, hf⟩ := (realizer.domain i).mp hi
      obtain ⟨c, X, R, hc, mx, ff⟩ := map i f hf
      obtain ⟨y, _, hxy⟩ := ff.2.1 x ((ep_at_read_l hq hc mx.1).mp hx)
      exact ⟨y, (sat a y).mpr ⟨i, x, f, hp, hf, hxy⟩⟩)
    (fun a _ u v hu hv => by
      obtain ⟨i, x, f, hp, hf, hxu⟩ := (sat a u).mp hu
      obtain ⟨j, y, g, hp', hg, hyv⟩ := (sat a v).mp hv
      obtain ⟨rfl, rfl⟩ := kpair_injective_l M hp hp'
      have eq := realizer.function.2 i g f hg hf
      obtain ⟨_, _, _, _, _, ff⟩ := map i f hf
      exact (fn0_function_l (ZF.modelsKP hZF) ff).1.2 x u v hxu (eq ▸ hyv))
    (fun a y _ hy => by
      obtain ⟨i, x, f, _, hf, hxy⟩ := (sat a y).mp hy
      obtain ⟨_, _, _, _, _, ff⟩ := map i f hf
      exact (ff.bound_l hxy).2)
  have read a i x f y (hp : KPair_d M a i x) (hf : Rd_entry_d i f P) (hy : Rd_entry_d a y r) : Rd_entry_d x y f := by
    obtain ⟨j, z, g, hp', hg, hzy⟩ := (sat a y).mp ((rs a y).mp hy).2
    obtain ⟨rfl, rfl⟩ := kpair_injective_l M hp hp'
    exact realizer.function.2 i g f hg hf ▸ hzy
  have compatible a b u v (hab : Rd_entry_d a b H) (hau : Rd_entry_d a u r) (hbv : Rd_entry_d b v r) : u = v := by
    obtain ⟨i, x, f, hp, hf, hxu⟩ := (sat a u).mp ((rs a u).mp hau).2
    obtain ⟨j, y, g, hp', hg, hyv⟩ := (sat b v).mp ((rs b v).mp hbv).2
    obtain ⟨k, hk, hxy⟩ := ((s.arrows a b i j x y hp hp').mp hab).2.2
    obtain ⟨_, _, _, _, _, ff⟩ := map i f hf
    exact (fn0_function_l (ZF.modelsKP hZF) ff).1.2 x u v hxu (realizer.commute i j k f g hk hf hg x y v hxy hyv)
  have preserve a b i u v (_ : Rd_entry_d a i p) (_ : Rd_entry_d b i p)
      (hau : Rd_entry_d a u r) (hbv : Rd_entry_d b v r) (hab : Rd_entry_d a b R) : Rd_entry_d u v V := by
    obtain ⟨_, _, k, x, y, hp, hp', hxy⟩ := (s.tags.relations a b).mp hab
    obtain ⟨j, z, f, hpa, hf, _⟩ := (sat a u).mp ((rs a u).mp hau).2
    obtain ⟨rfl, rfl⟩ := kpair_injective_l M hp hpa
    obtain ⟨c, X, R₀, hc, mx, _⟩ := map k f hf
    exact (realizer.maps k f c X R₀ hf hc mx).2 x y u v (read a k x f u hp hf hau)
      (read b k y f v hp' hf hbv) ((ep_rel_read_l hq hc mx.1).mp hxy)
  exact (di_cone_wf_l hZF s.system limit (fn0_of_function_l (ZF.modelsKP hZF) hr) wf compatible preserve).elim
    fun _ hh => hh.2.2

theorem it_realized_branch_l {ω α T Q G B Y V P : M.Domain} (hω : M.IsOmega ω)
    (h : It_diagram_d hZF ω α T Q G) (b : It_branch_d α T B) (ne : ∃ i, M.mem i B)
    (realizer : It_realizer_d hZF B Q G Y V P) (wf : Wf_rel_d Y V) : It_wf_branch_d hZF ω α T Q G B := by
  obtain ⟨L, A, p, H, R, q, c, C, S, ls, s, elem, limit, model⟩ := it_branch_data_l hZF hω h b ne
  exact ⟨b, L, A, p, H, R, q, c, C, S, ls, s, elem, limit, model,
    it_realizer_wf_l hZF h b.subset s limit realizer wf⟩

/-- 共尾枝由最小后继递归构造，良基性由实际相容腿证明；两步都只用 ZF。 -/
theorem it_pruned_wf_branch_l {ω α T Q G F a Y V P : M.Domain} (hω : M.IsOmega ω)
    (h : It_diagram_d hZF ω α T Q G) (cf : M.IsCofinalOrdinalSequence I F ω α) (ha : M.mem a α)
    (pruned : ∀ i k, M.mem i α → M.mem k α → ∃ j, M.mem j α ∧ Rd_entry_d i j T ∧ (k = j ∨ M.mem k j))
    (realizer : It_realizer_d hZF α Q G Y V P) (wf : Wf_rel_d Y V) :
    ∃ B, It_wf_branch_d hZF ω α T Q G B ∧ M.mem a B := by
  obtain ⟨B, b, haB⟩ := it_cofinal_branch_l hZF hω h.order cf ha pruned
  obtain ⟨P', rp, _⟩ := realizer.restrict_l hZF b.subset
  exact ⟨B, it_realized_branch_l hZF hω h b ⟨a, haB⟩ rp wf, haB⟩

end YesMetaZFC.SetTheory.LargeCardinal
