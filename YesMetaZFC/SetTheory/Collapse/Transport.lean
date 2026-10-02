import YesMetaZFC.SetTheory.Collapse.Mostowski
import YesMetaZFC.SetTheory.InnerModel.Separation.Formula
import YesMetaZFC.Model.SetTheory.Internal.Source

/-! # 集合编码同构的原公式传输

先用既有原子消去，再对原纯公式归纳。量词见证直接通过集合图的全域性和
满射性搬运；无需选择一个外部不可计算的同构函数。
-/

namespace YesMetaZFC.SetTheory
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {X B F : M.Domain}

theorem Mc_iso_d.core_formula_l (h : Mc_iso_d X B F)
    (hX : Nonempty {x : M.Domain // M.mem x X}) (hB : Nonempty {x : M.Domain // M.mem x B})
    {n} (φ : Formula 0 n) (hφ : φ.FreeClosed) (ρ : Env (rt_model_l X hX) n) (η : Env (rt_model_l B hB) n)
    (he : ∀ i, Rd_entry_d (ρ.bound i).val (η.bound i).val F) :
    Definitional.Semantics.satisfies Semantics.interpretation ρ φ ↔
      Definitional.Semantics.satisfies Semantics.interpretation η φ := by
  induction φ <;> simp only [Definitional.Formula.FreeClosed] at hφ <;>
    simp only [Definitional.Semantics.satisfies]
  case mem s t =>
    obtain ⟨i, rfl⟩ := rt_term_l s hφ.1
    obtain ⟨j, rfl⟩ := rt_term_l t hφ.2
    exact h.member _ _ _ _ (he i) (he j)
  case atom r hr ts => cases r <;> cases hr
  case neg φ ih => exact not_congr (ih hφ ρ η he)
  case conj φ ψ ih jh => exact and_congr (ih hφ.1 ρ η he) (jh hφ.2 ρ η he)
  case disj φ ψ ih jh => exact or_congr (ih hφ.1 ρ η he) (jh hφ.2 ρ η he)
  case imp φ ψ ih jh => exact imp_congr (ih hφ.1 ρ η he) (jh hφ.2 ρ η he)
  case iff φ ψ ih jh => exact iff_congr (ih hφ.1 ρ η he) (jh hφ.2 ρ η he)
  case forallE φ ih =>
    constructor
    · intro hs y
      obtain ⟨a, ha⟩ := h.onto y.val y.property
      let x : (rt_model_l X hX).Domain := ⟨a, (h.function.bound_l ha).1⟩
      exact (ih hφ (ρ.push x) (η.push y) (Fin.cases ha he)).mp (hs x)
    · intro hs x
      obtain ⟨b, hb, hab⟩ := h.function.2.1 x.val x.property
      let y : (rt_model_l B hB).Domain := ⟨b, hb⟩
      exact (ih hφ (ρ.push x) (η.push y) (Fin.cases hab he)).mpr (hs y)
  case existsE φ ih =>
    constructor
    · rintro ⟨x, hx⟩
      obtain ⟨b, hb, hab⟩ := h.function.2.1 x.val x.property
      let y : (rt_model_l B hB).Domain := ⟨b, hb⟩
      exact ⟨y, (ih hφ (ρ.push x) (η.push y) (Fin.cases hab he)).mp hx⟩
    · rintro ⟨y, hy⟩
      obtain ⟨a, ha⟩ := h.onto y.val y.property
      let x : (rt_model_l X hX).Domain := ⟨a, (h.function.bound_l ha).1⟩
      exact ⟨x, (ih hφ (ρ.push x) (η.push y) (Fin.cases ha he)).mpr hy⟩

theorem Mc_iso_d.formula_l (h : Mc_iso_d X B F)
    (hX : Nonempty {x : M.Domain // M.mem x X}) (hB : Nonempty {x : M.Domain // M.mem x B})
    {n} (φ : Formula 1 n) (hφ : φ.FreeClosed) (ρ : Env (rt_model_l X hX) n) (η : Env (rt_model_l B hB) n)
    (he : ∀ i, Rd_entry_d (ρ.bound i).val (η.bound i).val F) : Formula.satisfies ρ φ ↔ Formula.satisfies η φ :=
  (Internal.source_core_sat_l φ ρ).symm.trans ((h.core_formula_l hX hB (Internal.source_core_l φ)
    (Internal.source_core_closed_l φ hφ) ρ η he).trans (Internal.source_core_sat_l φ η))

/-- 有限参数赋值可逐项回拉，不选择整个模型上的逆函数。 -/
theorem Mc_iso_d.params_l (h : Mc_iso_d X B F)
    (hX : Nonempty {x : M.Domain // M.mem x X}) (hB : Nonempty {x : M.Domain // M.mem x B})
    {n} (η : Env (rt_model_l B hB) n) : ∃ ρ : Env (rt_model_l X hX) n,
      ∀ i, Rd_entry_d (ρ.bound i).val (η.bound i).val F := by
  have hn := hX
  obtain ⟨u⟩ := hn
  have liftParams {n} (v : Fin n → (rt_model_l B hB).Domain) :
      ∃ f : Fin n → (rt_model_l X hX).Domain, ∀ i, Rd_entry_d (f i).val (v i).val F := by
    induction n with
    | zero => exact ⟨Fin.elim0, fun i => Fin.elim0 i⟩
    | succ n ih =>
      obtain ⟨f, hf⟩ := ih (fun i => v i.succ)
      obtain ⟨a, ha⟩ := h.onto (v 0).val (v 0).property
      exact ⟨Fin.cases ⟨a, (h.function.bound_l ha).1⟩ f, Fin.cases ha hf⟩
  obtain ⟨f, hf⟩ := liftParams η.bound
  exact ⟨⟨f, fun _ => u⟩, hf⟩

end YesMetaZFC.SetTheory
