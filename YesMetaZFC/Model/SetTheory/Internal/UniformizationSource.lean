import YesMetaZFC.Model.SetTheory.Internal.SourceTheory
import YesMetaZFC.Model.SetTheory.Internal.SeparationSource

/-! # 原有界关系在源模型内的统一化

在已有乘积内分离满足关系，再对这一源内关系作有界选择。值域界由调用者
已有的数据给出，不调用无界统一化；函数图的坐标界只需两次并。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem sc_relation_source_l {ω c X R D C} (hω : M.IsOmega ω)
    (hX : M.TransitiveSet X) (hm : Smem_d I c X R) (theory : Sc_theory_d I ω X R)
    {p} (φ : BinarySchema p) (hd : φ.body.IsDelta0) (ρ : Env M p) (hρ : ∀ i, M.mem (ρ.bound i) X)
    (hD : M.mem D X) (hC : M.mem C X) : ∃ Q, M.mem Q X ∧ M.IsSetRelation I Q ∧
      ∀ x y, Rd_entry_d x y Q ↔ M.mem x D ∧ M.mem y C ∧ φ.denote ρ x y := by
  obtain ⟨P, hPX, product⟩ := theory.algebra.product D C hD hC
  let e : Fin (p+2) → Fin (p+5) := Fin.cases 0 (Fin.cases 1 (fun i => i.succ.succ.succ.succ.succ))
  let η := (ρ.push D).push C
  let ψ : UnarySchema (p+2) := {
    body := Formula.existsMem (.bound 2) (Formula.existsMem (.bound 2)
      (.conj (kpair0_m (.bound 2) (.bound 1) .newest) (φ.body.rename e)))
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed] }
  have point q x y : Formula.satisfies (((η.push q).push x).push y) (φ.body.rename e) ↔ φ.denote ρ x y :=
    (Formula.satisfies_rename ..).trans (Formula.closed_env_l φ.body φ.freeClosed
      (funext (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))))
  have sat q : ψ.denote η q ↔ ∃ x, M.mem x D ∧ ∃ y, M.mem y C ∧ KPair_d M q x y ∧ φ.denote ρ x y := by
    simp only [ψ, UnarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
      kpair0_sat_l hZF.1, point]; rfl
  obtain ⟨Q, hQX, spec⟩ := sc_separate_source_l I hZF hω hX hm theory ψ
    (.existsMem _ (.existsMem _ (.conj (kpair0_delta_l ..) (hd.rename_l e)))) η
    (Fin.cases hC (Fin.cases hD hρ)) hPX
  refine ⟨Q, hQX, fun q hq => ?_, fun x y => ⟨?_, ?_⟩⟩
  · obtain ⟨x, _, y, _, h⟩ := (product q).mp ((spec q).mp hq).1
    exact ⟨x, y, h⟩
  · rintro ⟨q, code, hq⟩
    obtain ⟨a, ha, b, hb, pair, h⟩ := (sat q).mp ((spec q).mp hq).2
    obtain ⟨rfl, rfl⟩ := kpair_injective_l M pair code
    exact ⟨ha, hb, h⟩
  · rintro ⟨hx, hy, hxy⟩
    obtain ⟨q, hq⟩ := (kp_pair_l (ZF.modelsKP hZF)).total x y
    exact ⟨q, hq, (spec q).mpr ⟨(product q).mpr ⟨x, hx, y, hy, hq⟩,
      (sat q).mpr ⟨x, hx, y, hy, hq, hxy⟩⟩⟩

theorem sc_uniform_source_l {ω c X R D C} (hω : M.IsOmega ω)
    (hX : M.TransitiveSet X) (hm : Smem_d I c X R) (theory : Sc_theory_d I ω X R)
    {p} (φ : BinarySchema p) (hd : φ.body.IsDelta0) (ρ : Env M p) (hρ : ∀ i, M.mem (ρ.bound i) X)
    (hD : M.mem D X) (hC : M.mem C X) (ht : ∀ x, M.mem x D → ∃ y, M.mem y C ∧ φ.denote ρ x y) :
    ∃ B, M.mem B X ∧ Fn0_d D C B ∧ ∀ x y, Rd_entry_d x y B → φ.denote ρ x y := by
  obtain ⟨Q, hQ, _, spec⟩ := sc_relation_source_l hZF hω hX hm theory φ hd ρ hρ hD hC
  obtain ⟨B, hB, hf, sub⟩ := theory.algebra.choice D C Q hD hC hQ (fun x hx => by
    obtain ⟨y, hy, hxy⟩ := ht x hx
    exact ⟨y, hy, (spec x y).mpr ⟨hx, hy, hxy⟩⟩)
  exact ⟨B, hB, hf, fun x y ⟨q, code, hq⟩ => ((spec x y).mp ⟨q, code, sub q hq⟩).2.2⟩

/-- 两次并给出的坐标界内可以分离精确值域；关系无需单值。 -/
theorem sc_range_source_l {ω c X R F : M.Domain} (hω : M.IsOmega ω)
    (hX : M.TransitiveSet X) (hm : Smem_d I c X R) (theory : Sc_theory_d I ω X R)
    (hF : M.mem F X) : ∃ C, M.mem C X ∧ M.IsRangeOf I C F := by
  obtain ⟨P, hP, coords⟩ := theory.algebra.envelope_l hF
  let ρ : Env M 2 := ⟨Fin.cases F (fun _ => P), fun _ => F⟩
  let φ : UnarySchema 2 := { body := Formula.existsMem (.bound 2) (rd_entry0_m .newest (.bound 1) (.bound 2)) }
  have sat b : φ.denote ρ b ↔ ∃ a, M.mem a P ∧ Rd_entry_d a b F := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_existsMem_iff, rd_entry0_sat_l hZF.1]; rfl
  obtain ⟨C, hC, spec⟩ := sc_separate_source_l I hZF hω hX hm theory φ
    (.existsMem _ (rd_entry0_delta_l ..)) ρ (Fin.cases hF (fun _ => hP)) hP
  exact ⟨C, hC, fun b => (spec b).trans ((and_congr_right fun _ => sat b).trans
    ⟨fun ⟨_, a, _, h⟩ => ⟨a, h⟩, fun ⟨a, h⟩ => ⟨(coords a b h).2, a, (coords a b h).1, h⟩⟩)⟩

/-- 每个源对象都有实际源内常值代表，并保留源内值域界。 -/
theorem sc_constant_l {ω c X R D x} (hω : M.IsOmega ω)
    (hX : M.TransitiveSet X) (hm : Smem_d I c X R) (theory : Sc_theory_d I ω X R)
    (hD : M.mem D X) (hx : M.mem x X) : ∃ g C, M.mem g X ∧ M.mem C X ∧ Fn0_d D C g ∧
      ∀ a y, Rd_entry_d a y g ↔ M.mem a D ∧ y = x := by
  let φ : BinarySchema 1 := { body := Formula.extensionalEq .newest (.bound 2) }
  let ρ : Env M 1 := ⟨fun _ => x, fun _ => x⟩
  have sat a y : φ.denote ρ a y ↔ y = x := Formula.satisfies_extensionalEq_iff_eq hZF.1 ..
  obtain ⟨C, hC, hc⟩ := theory.algebra.pair x x hx hx
  obtain ⟨g, hg, hf, hs⟩ := sc_uniform_source_l hZF hω hX hm theory φ (.atom _ _ _)
    ρ (fun _ => hx) hD hC (fun a _ => ⟨x, (hc x).mpr (Or.inl rfl), (sat a x).mpr rfl⟩)
  refine ⟨g, C, hg, hC, hf, fun a y => ⟨fun h => ⟨(hf.bound_l h).1, (sat a y).mp (hs a y h)⟩, ?_⟩⟩
  rintro ⟨ha, rfl⟩
  obtain ⟨y, _, hy⟩ := hf.2.1 a ha
  exact (sat a y).mp (hs a y hy) ▸ hy

/-- 已在源中的函数图也有源内值域界，因而属于代码化函数域。 -/
theorem sc_function_domain_l {X D F : M.Domain} (algebra : Sc_algebra_d X)
    (hF : M.mem F X) (hf : Fn0_d D X F) : Sfun_d X D F := by
  obtain ⟨C, hC, bound⟩ := algebra.envelope_l hF
  exact ⟨hF, C, hC, hf.retarget_l (fun a b hab => (bound a b hab).2)⟩

/-- 逐项读取源内函数图的首坐标，再分离出精确的定义域。 -/
theorem sc_function_domain_mem_l {ω c X R A B F : M.Domain} (hω : M.IsOmega ω)
    (hX : M.TransitiveSet X) (hm : Smem_d I c X R) (theory : Sc_theory_d I ω X R)
    (hF : M.mem F X) (hf : Fn0_d A B F) : M.mem A X := by
  obtain ⟨C, hCX, coords⟩ := theory.algebra.envelope_l hF
  have bound a (ha : M.mem a A) : M.mem a C := by
    obtain ⟨b, _, hab⟩ := hf.2.1 a ha
    exact (coords a b hab).1
  let η : Env M 1 := ⟨fun _ => F, fun _ => F⟩
  let ψ : UnarySchema 1 := {
    body := Formula.existsMem (.bound 1) (Formula.existsMem .newest
      (Formula.existsMem .newest (kpair0_m (.bound 2) (.bound 3) .newest))) }
  have read a : ψ.denote η a ↔ ∃ p, M.mem p F ∧ ∃ t, M.mem t p ∧ ∃ b, M.mem b t ∧ KPair_d M p a b := by
    simp only [ψ, UnarySchema.denote, Formula.satisfies_existsMem_iff, kpair0_sat_l hZF.1]; rfl
  obtain ⟨D, hDX, spec⟩ := sc_separate_source_l I hZF hω hX hm theory ψ
    (.existsMem _ (.existsMem _ (.existsMem _ (kpair0_delta_l ..)))) η (fun _ => hF) hCX
  have eq : D = A := hZF.1.eq_of_same_members D A (fun a => by
    rw [spec a, read a]
    refine ⟨fun ⟨_, p, hp, _, _, b, _, hab⟩ => (hf.bound_l ⟨p, hab, hp⟩).1, fun ha => ?_⟩
    obtain ⟨b, _, p, hp, hpf⟩ := hf.2.1 a ha
    obtain ⟨t, ht, hb⟩ := (kpair_union_l M hp b).mpr (Or.inr rfl)
    exact ⟨bound a ha, p, hpf, t, ht, b, hb, hp⟩)
  exact eq ▸ hDX

end YesMetaZFC.SetTheory.Internal
