import YesMetaZFC.Model.Forcing.Internal.Homogeneous.Basic
import YesMetaZFC.SetTheory.InnerModel.OD.Parameters

/-! # 地参数力迫的原公式

先量化正条件，再用有限存在块量化其 check 名称参数，最后调用原力迫翻译。
因而 Gforce 仅依赖完整力迫呈现与原地参数，不携带泛型或名称选择函数。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel
universe u

def gforce_m {n d} (φ : Formula 1 n) (B R z : Term d) (e : Fin n → Term d) : Formula 1 d :=
  .existsE (.conj (.mem .newest B.weaken)
    (.conj (.neg (Formula.extensionalEq .newest z.weaken))
      (od_ex_m n (.conj
        (lr_and_m (fun i : Fin n => check_m (lr_shift_l n .newest)
          (lr_shift_l n (e i).weaken) (.bound ⟨i.val, by omega⟩)))
        (force_at_m φ (fun i => .bound ⟨i.val, by omega⟩)
          (lr_shift_l n B.weaken) (lr_shift_l n R.weaken) (lr_shift_l n z.weaken)
          (lr_shift_l n .newest))))))

@[simp] theorem gforce_closed_l {n d} (φ : Formula 1 n) (B R z : Term d) (e : Fin n → Term d)
    (hφ : φ.FreeClosed) (hB : B.freeSupport = []) (hR : R.freeSupport = [])
    (hz : z.freeSupport = []) (he : ∀ i, (e i).freeSupport = []) : (gforce_m φ B R z e).FreeClosed := by
  simp only [gforce_m, Definitional.Formula.FreeClosed]
  refine ⟨⟨rfl, by simpa using hB⟩,
    (Formula.extensionalEq_freeClosed_iff _ _).mpr ⟨rfl, by simpa using hz⟩, od_ex_closed_l n _ ?_⟩
  simp only [Definitional.Formula.FreeClosed]
  refine ⟨?_, force_at_closed_l _ _ _ _ _ _ hφ (fun _ => rfl)
    (by simpa using hB) (by simpa using hR) (by simpa using hz) (by simp)⟩
  exact lr_and_closed_l _ (fun i => check_m_freeClosed _ _ _ (by simp) (by simpa using he i) rfl)

theorem gforce_sat_l {M : SetTheory.Structure.{u}} (hE : Extensional M) {n d}
    (φ : Formula 1 n) (hφ : φ.FreeClosed) (ρ : Env M d) (B R z : Term d) (e : Fin n → Term d) :
    Formula.satisfies ρ (gforce_m φ B R z e) ↔
      Gforce_d M (B.eval ρ) (R.eval ρ) (z.eval ρ) φ (fun i => (e i).eval ρ) := by
  simp only [gforce_m, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_neg_iff, Formula.satisfies_extensionalEq_iff_eq hE,
    od_ex_sat_l, lr_and_sat_l, check_sat_l M hE, force_at_sat_l, lr_shift_sat_l,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  simp only [Definitional.Term.eval, lr_env_bound_l, lr_env_free_l]
  constructor
  · rintro ⟨p, hp, hpz, v, hv, hf⟩
    exact ⟨p, ⟨v, ρ.free⟩, hp, hpz, hv, hf⟩
  · rintro ⟨p, η, hp, hpz, hη, hf⟩
    exact ⟨p, hp, hpz, η.bound, hη,
      (forces_env_l hE φ hφ η ⟨η.bound, ρ.free⟩ (fun _ => rfl) p).mp hf⟩

end YesMetaZFC.Model.Forcing.Internal
