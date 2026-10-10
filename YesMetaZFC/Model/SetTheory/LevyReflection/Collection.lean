import YesMetaZFC.Model.SetTheory.LevyReflection.WitnessSyntax

/-! # ZF 中全部有限参数组的统一见证界

以 X^ω 中的实际赋值图为收集域。每个图的指定有限坐标唯一确定参数，故可收集
各纤维的一件见证，再取并。没有使用对象理论选择公理或外部标准性。
-/

namespace YesMetaZFC.SetTheory
open Definitional.Project Internal
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)
include I

theorem ZF.lr_bound_exists_l (hZF : M.Models ZF) {ω} (hω : M.IsOmega ω)
    (A : M.Domain) {n} (φ : UnarySchema n) : ∃ Y, Lr_bound_d φ A Y := by
  classical
  obtain ⟨a⟩ := M.nonempty
  obtain ⟨X, hAX⟩ := KP.exists_insert (modelsKP hZF) A a
  have hX : ∃ x, M.mem x X := ⟨a, (hAX a).mpr (Or.inr rfl)⟩
  obtain ⟨v, hv⟩ := Classical.axiomOfChoice (fun i : Fin n => num_exists_l (modelsKP hZF) i.val)
  have hvω i := num_mem_l hZF.1 hω (hv i)
  have hinj : Function.Injective v := fun i j hij => Fin.ext
    (num_injective_l (modelsKP hZF) (hv i) (hij.symm ▸ hv j))
  obtain ⟨E, hE⟩ := exists_functionSpace hZF I ω X
  let ρ : Env M (n+1) := ⟨Fin.cases X v, fun _ => X⟩
  let ψ : BinarySchema (n+1) := {
    body := lr_fiber_m (𝒞 := 𝒞) φ (fun i => .bound ⟨i.val+3, by omega⟩) (.bound 2) (.bound 1) .newest }
  have hψ f Y : ψ.denote ρ f Y ↔ Lr_fiber_d I φ v X f Y := lr_fiber_sat_l I φ _ _ _ _ _
  obtain ⟨C, hC⟩ := collection_exists_d hZF ψ ρ E (by
    intro f hf
    have hf := (hE f).mp hf
    obtain ⟨p, hp⟩ := Classical.axiomOfChoice (fun i => hf.2.2 (v i) (hvω i))
    let η : Env M n := ⟨p, ρ.free⟩
    have same (δ : Env M n) (hd : ∀ i, M.PairMember I (v i) (δ.bound i) f) (x : M.Domain) :
        φ.denote δ x ↔ φ.denote η x := lr_env_congr_l φ.body φ.freeClosed (δ.push x) (η.push x)
          (Fin.cases rfl (fun i => (hf.1.2 (v i) (p i) (δ.bound i) (hp i).2 (hd i)).symm))
    by_cases hex : ∃ x, φ.denote η x
    · obtain ⟨x, hx⟩ := hex
      obtain ⟨Y, hY⟩ := KP.exists_pair (modelsKP hZF) x x
      exact ⟨Y, (hψ f Y).mpr (fun δ _ hd _ => ⟨x, (hY x).mpr (Or.inl rfl), (same δ hd x).mpr hx⟩)⟩
    · obtain ⟨Y, _⟩ := KP.exists_empty (modelsKP hZF)
      exact ⟨Y, (hψ f Y).mpr (fun δ _ hd ⟨x, hx⟩ => (hex ⟨x, (same δ hd x).mp hx⟩).elim)⟩)
  obtain ⟨Y, hY⟩ := KP.exists_union (modelsKP hZF) C
  refine ⟨Y, fun η hη hx => ?_⟩
  have hηX i := (hAX (η.bound i)).mpr (Or.inl (hη i))
  obtain ⟨f, hf, hp⟩ := senv_params_l I hZF hE hX v η.bound hinj hvω hηX
  obtain ⟨Z, hZ, hz⟩ := hC f hf
  obtain ⟨x, hxZ, hφ⟩ := (hψ f Z).mp hz η hηX hp hx
  exact ⟨x, (hY x).mpr ⟨Z, hZ, hxZ⟩, hφ⟩

end YesMetaZFC.SetTheory
