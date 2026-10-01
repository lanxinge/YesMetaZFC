import YesMetaZFC.Model.Forcing.Proper.Generic.WitnessSyntax
import YesMetaZFC.Model.SetTheory.LevyReflection

/-! # 由有限反射统一取得 N 中的见证池

只反射“完整池方程”和其存在式两条固定原公式；它们的参数槽位全部开放。
因此同一个内部初等 N 对任意来自 N 的名称参数均含实际见证池及判定集。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}} {B R z : M.Domain}

theorem ng_witness_reflect_l (hZF : M.Models ZF) {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)
    {ω c d X T N S} (hω : M.IsOmega ω) (hS : Ssub_d I c d X T N S) (hN : Selem_d I ω c d)
    (hT : ∀ x y, M.PairMember I x y T ↔ M.mem x X ∧ M.mem y X ∧ M.mem x y)
    (hX : M.TransitiveSet X) (hB : M.mem B N) (hR : M.mem R N) (hz : M.mem z N)
    {n} (φ : UnarySchema n) (hData : Lr_reflect_d (ng_data_m φ) X) (hExists : Lr_reflect_d (ng_exists_m φ) X)
    (ρ : Env M n) (hρ : ∀ i, M.mem (ρ.bound i) N) :
    ∃ A D, M.mem A N ∧ M.mem D N ∧ Ng_witness_d (B := B) (R := R) (z := z) φ ρ A D := by
  let L := smdl_structure_l I (R := T) hS.source.2.1
  let K := smdl_structure_l I (R := S) hS.target.2.1
  let δ := ((ρ.push B).push R).push z
  have hd : ∀ i, M.mem (δ.bound i) N := Fin.cases hz (Fin.cases hR (Fin.cases hB hρ))
  let θ : Env L (n+3) := ⟨fun i => ⟨δ.bound i, hS.subset _ (hd i)⟩, fun _ => ⟨B, hS.subset _ hB⟩⟩
  let η : Env K (n+3) := ⟨fun i => ⟨δ.bound i, hd i⟩, fun _ => ⟨B, hB⟩⟩
  let ψ : UnarySchema (n+3) := { body := .existsE (ng_data_m φ) }
  let χ : UnarySchema (n+4) := { body := ng_data_m φ }
  obtain ⟨A, D, ha⟩ := ng_witness_data_l (B := B) (R := R) (z := z) hZF φ ρ
  have hex : Formula.satisfies δ (ng_exists_m φ) :=
    (Formula.satisfies_exists_iff δ ψ.body).mpr ⟨A,
      (Formula.satisfies_exists_iff (δ.push A) χ.body).mpr ⟨D, (ng_data_sat_l hZF.1 φ ρ B R z A D).mpr ha⟩⟩
  have hl := (lr_model_l I hS.source hT hX (ng_exists_m φ) (ng_exists_closed_l φ) hExists δ θ (fun _ => rfl)).mp hex
  obtain ⟨a, ha⟩ := selem_witness_l I hZF hω hS hN ψ θ η (fun _ => rfl)
    ((Formula.satisfies_exists_iff θ ψ.body).mp hl)
  let a' : L.Domain := ⟨a.val, hS.subset a.val a.property⟩
  obtain ⟨b, hb⟩ := selem_witness_l I hZF hω hS hN χ (θ.push a') (η.push a)
    (Fin.cases rfl (fun _ => rfl)) ((Formula.satisfies_exists_iff (θ.push a') χ.body).mp ha)
  let b' : L.Domain := ⟨b.val, hS.subset b.val b.property⟩
  have hbody := (lr_model_l I hS.source hT hX (ng_data_m φ) (ng_data_closed_l φ) hData
    ((δ.push a.val).push b.val) ((θ.push a').push b') (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))).mpr hb
  exact ⟨a.val, b.val, a.property, b.property, (ng_data_sat_l hZF.1 φ ρ B R z a.val b.val).mp hbody⟩

end YesMetaZFC.Model.Forcing.Internal
