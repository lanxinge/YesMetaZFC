import YesMetaZFC.Model.SetTheory.Relations.OmegaCut
import YesMetaZFC.Model.SetTheory.Relations.Parity
import YesMetaZFC.Model.SetTheory.Internal.SmallSkolemSyntax

/-! # 两个原关系模型之间的有界函数回收

所属切片中的实际乘积经有界公式读到当前模型。当前函数图是该乘积的
子集，子集封闭遂把整个函数码放回同一实现像，再反向读取其函数性。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem rr_cross_capture_l {N T Γ Y S H k : M.Domain}
    (nx : ∃ x, M.mem x N) (ny : ∃ y, M.mem y Y)
    (hN : (smdl_structure_l I (R := T) nx).Models KP)
    (ey : Extensional (smdl_structure_l I (R := S) ny))
    (U d a p : (smdl_structure_l I (R := T) nx).Domain)
    (trans : (smdl_structure_l I (R := T) nx).TransitiveSet U)
    (carrier : ∀ x, M.mem x Γ ↔ M.mem x N ∧ M.PairMember I x U.val T)
    (fk : M.IsSetInjectionFromTo I k Γ Y)
    (image : ∀ y, M.PairMember I y H S ↔ ∃ x, M.mem x Γ ∧ M.PairMember I x y k)
    (pred : ∀ x y, M.PairMember I x y k → ∀ z, M.PairMember I z y S ↔ ∃ b, M.PairMember I b x T ∧ M.PairMember I b z k)
    (closed : Rr_closed_d I Y S H)
    (hp : (smdl_structure_l I (R := T) nx).mem p U)
    (product : (smdl_structure_l I (R := T) nx).IsCartesianProduct (kp_pair_l hN) p d a)
    (d' a' f' : (smdl_structure_l I (R := S) ny).Domain)
    (hd : M.PairMember I d.val d'.val k) (ha : M.PairMember I a.val a'.val k) (fn : Fn0_d d' a' f') :
    ∃ f : (smdl_structure_l I (R := T) nx).Domain,
      (smdl_structure_l I (R := T) nx).mem f U ∧ M.PairMember I f.val f'.val k ∧ Fn0_d d a f := by
  let N₀ := smdl_structure_l I (R := T) nx
  let Y₀ := smdl_structure_l I (R := S) ny
  have hdU : N₀.mem d U := ((carrier d.val).mp (fk.1.input_mem_of_pairMember hd)).2
  have haU : N₀.mem a U := ((carrier a.val).mp (fk.1.input_mem_of_pairMember ha)).2
  obtain ⟨P, hP, hpP⟩ := fk.1.2.2 p.val ((carrier p.val).mpr ⟨p.property, hp⟩)
  let p' : Y₀.Domain := ⟨P, hP⟩
  let nu : Nonempty {x : N₀.Domain // N₀.mem x U} := ⟨⟨d, hdU⟩⟩
  let ρ : Env (rt_model_l U nu) 3 :=
    ⟨Fin.cases ⟨p, hp⟩ (Fin.cases ⟨a, haU⟩ (fun _ => ⟨d, hdU⟩)), fun _ => ⟨d, hdU⟩⟩
  let η : Env Y₀ 3 := ⟨Fin.cases p' (Fin.cases a' (fun _ => d')), fun _ => d'⟩
  have moved := (rr_native_delta_l I nx ny U trans nu carrier fk pred
    (sh_product_m .newest (.bound 2) (.bound 1)) (by simp -implicitDefEqProofs)
    (sh_product_delta_l ..) ρ η (Fin.cases hpP (Fin.cases ha (fun _ => hd)))).mp
      ((sh_product_sat_l hN ..).mpr product)
  simp only [sh_product_m, Formula.satisfies_conj_iff, Formula.satisfies_forallMem_iff,
    Formula.satisfies_existsMem_iff, kpair0_sat_l ey] at moved
  have sub (z : Y₀.Domain) (hz : Y₀.mem z f') : Y₀.mem z p' := by
    obtain ⟨x, hx, y, hy, pair⟩ := fn.1 z hz
    obtain ⟨v, hv, pair'⟩ := moved.2 x hx y hy
    exact kpair_unique_l Y₀ ey pair' pair ▸ hv
  have hpH := (image P).mpr ⟨p.val, (carrier p.val).mpr ⟨p.property, hp⟩, hpP⟩
  obtain ⟨F, hF, hFf⟩ := (image f'.val).mp
    (closed P f'.val hP f'.property hpH (fun z hz edge => sub ⟨z, hz⟩ edge))
  let f : N₀.Domain := ⟨F, ((carrier F).mp hF).1⟩
  have hfU : N₀.mem f U := ((carrier F).mp hF).2
  let σ : Env (rt_model_l U nu) 3 :=
    ⟨Fin.cases ⟨f, hfU⟩ (Fin.cases ⟨a, haU⟩ (fun _ => ⟨d, hdU⟩)), fun _ => ⟨d, hdU⟩⟩
  let τ : Env Y₀ 3 := ⟨Fin.cases f' (Fin.cases a' (fun _ => d')), fun _ => d'⟩
  have read := rr_native_delta_l I nx ny U trans nu carrier fk pred (fn0_m (.bound 2) (.bound 1) .newest)
    (by simp -implicitDefEqProofs) (fn0_delta_l ..) σ τ (Fin.cases hFf (Fin.cases ha (fun _ => hd)))
  exact ⟨f, hfU, hFf, (fn0_sat_l hN.1 ..).mp (read.mpr ((fn0_sat_l ey ..).mpr fn))⟩


/-- 共同切片内某个原对象的子集封闭传到当前模型的全部新子集。 -/
theorem rr_cross_closed_l {N T Γ Y S H k b : M.Domain}
    (nx : ∃ x, M.mem x N) (U β : (smdl_structure_l I (R := T) nx).Domain)
    (trans : (smdl_structure_l I (R := T) nx).TransitiveSet U)
    (carrier : ∀ x, M.mem x Γ ↔ M.mem x N ∧ M.PairMember I x U.val T)
    (fk : M.IsSetInjectionFromTo I k Γ Y)
    (image : ∀ y, M.PairMember I y H S ↔ ∃ x, M.mem x Γ ∧ M.PairMember I x y k)
    (pred : ∀ x y, M.PairMember I x y k → ∀ z,
      M.PairMember I z y S ↔ ∃ a, M.PairMember I a x T ∧ M.PairMember I a z k)
    (closed : Rr_closed_d I Y S H) (hβb : M.PairMember I β.val b k)
    (source : Rr_closed_d I N T β.val) : Rr_closed_d I Y S b := by
  let N₀ := smdl_structure_l I (R := T) nx
  intro E P hE hP hEB sub
  obtain ⟨x, hx, hxE⟩ := (pred β.val b hβb E).mp hEB
  have hxΓ := fk.1.input_mem_of_pairMember hxE
  have hEH := (image E).mpr ⟨x, hxΓ, hxE⟩
  obtain ⟨z, hz, hzP⟩ := (image P).mp (closed E P hE hP hEH sub)
  have sub' a (haN : M.mem a N) (haz : M.PairMember I a z T) : M.PairMember I a x T := by
    obtain ⟨a', ha', haa⟩ := fk.1.2.2 a ((carrier a).mpr ⟨haN,
      trans (⟨z, ((carrier z).mp hz).1⟩ : N₀.Domain) ((carrier z).mp hz).2 ⟨a, haN⟩ haz⟩)
    obtain ⟨u, hu, hua⟩ := (pred x E hxE a').mp (sub a' ha' ((pred z P hzP a').mpr ⟨a, haz, haa⟩))
    exact fk.2 u a a' hua haa ▸ hu
  exact (pred β.val b hβb P).mpr ⟨z, source x z ((carrier x).mp hxΓ).1 ((carrier z).mp hz).1 hx sub', hzP⟩

end YesMetaZFC.SetTheory.Internal
