import YesMetaZFC.SetTheory.LargeCardinal.ExtenderRawLow
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderReadLayer
import YesMetaZFC.Model.SetTheory.Internal.SourceHierarchy
import YesMetaZFC.Model.SetTheory.Internal.RelationLayerSeparation
import YesMetaZFC.Model.SetTheory.Internal.SourcePower

/-! # 新共同层的相对秩与递归闭包

新层只用所属侧的有界坍塌；相对秩直接沿原关系常值嵌入传输。
低层之间的实际图由完整前驱实现构造，并逐点交换。整个后继无需
所属模型的整体传递超幂，也不要求原关系极限预先良基。对于含 ω 的
极限共同层，还输出下一层的全部内部有限读写闭包及同一 ω 的固定性。
全内部分离由原关系分离和完整前驱回收构造；相对幂集从原层的实际
幂集证书传输。新层模型码、源理论和相对幂集均作为后继结果返回。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem er_rank_successor_l {ω c X R c' Y S q H N κ K L F R₀ Γ γ k B D Q Γ' e α : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (mx : Smem_d I c X R)
    (theory : Sc_theory_d I ω X R) (collection : Sc_collection_d I ω X R)
    (model : Smdl_d I c' Y S) (hq : Smap_d I ω c c' X Y q)
    (small : Rr_small_d I Y S H) (closed : Rr_closed_d I Y S H)
    (owner : Ep_source_d hZF ω κ K N R₀) (hΓ : M.mem Γ N) (rank : Vr_d N γ Γ)
    (hγ : M.IsLimitOrdinal γ) (hκ : M.mem κ Γ) (fk : M.IsSetInjectionFromTo I k Γ Y)
    (image : ∀ z, Rd_entry_d z H S ↔ ∃ x, M.mem x Γ ∧ Rd_entry_d x z k)
    (pred : ∀ x z, Rd_entry_d x z k → ∀ w, Rd_entry_d w z S ↔ ∃ y, M.mem y x ∧ Rd_entry_d y w k)
    (family : Em_source_d ω κ L N F) (coherent : Ec_source_d I ω κ L N F) (above : M.MemberSubset ω L)
    (hB : M.mem B Γ) (hα : M.mem α Γ) (rankB : Vr_d N α B)
    (height : M.IsLimitOrdinal α) (omega : M.mem ω B) (power : Sc_power_d B)
    (owned : Eb_collapse_d ω κ L K N B F D Q Γ' e) :
    ∃ J O Z A p T V r o C W j q' k' H' σ a₁ R₁, Er_system_d I ω κ L Y S F k J O Z A p T V ∧
      Di_limit_d A p T V r C W ∧ Smdl_d I o C W ∧ Di_elementary_d I ω O A p T V ∧
      Smap_d I ω c' o Y C j ∧ Smap_d I ω c o X C q' ∧
      (Zc_model_d I ω c X R → Zc_model_d I ω o C W) ∧
      (∀ x z, Rd_entry_d x z q' ↔ M.mem x X ∧ ∃ y, Rd_entry_d x y q ∧ Rd_entry_d y z j) ∧
      Rr_layer_d I Γ' C W H' k' ∧ M.IsSetInjectionFromTo I σ B Γ' ∧
      (∀ x E, Rd_entry_d x E k' ↔ ∃ u, M.mem u D ∧ Rd_entry_d u x e ∧ Er_value_d κ Γ Y k r u E) ∧
      (∀ x y z, Rd_entry_d x y σ → Rd_entry_d x z k → ∀ w,
        Rd_entry_d z w j ↔ Rd_entry_d y w k') ∧
      Fs_read_d ω Γ' ∧ (∀ a, M.mem a Γ' → ∃ p, M.mem p Γ' ∧ M.IsUnionOf p a) ∧
      Rd_entry_d ω ω σ ∧
      Smem_d I a₁ Γ' R₁ ∧ Sc_theory_d I ω Γ' R₁ ∧ Sc_power_d Γ' ∧
      Rr_closed_d I C W H' ∧ Rr_small_d I C W H' ∧
      ∃ a a', Rd_entry_d α a k ∧ Rd_entry_d a a' j ∧ Rr_rank_d I C W a' H' := by
  have hBN := owner.transitive Γ hΓ B hB
  have trans := rankB.transitive_l hZF owner.transitive hBN
  obtain ⟨J, O, Z, A, p, T, V, r, o, C, W, j, q', k', H', system, limit, next, elem,
    embed, root, certificate, comp, _, layer, graph, _, b, hBb, hbH⟩ :=
    er_successor_l hZFC hω hX mx theory collection model hq small closed owner hΓ rank hγ hκ fk image pred
      family coherent above hB trans owned
  have low := rank.transitive_l hZF owner.transitive hΓ
  obtain ⟨v, hv, hκv⟩ := fk.1.2.2 κ hκ
  have hH : M.mem H Y := (model.2.2.2 v H ((image v).mpr ⟨κ, hκ, hκv⟩)).2
  let current : Rr_layer_d I Γ Y S H k := ⟨low, hH, fk, image, pred⟩
  obtain ⟨t, left, restrict⟩ := current.restrict_l I hZF trans hBb
  -- 在两个已实现低层之间构造真实函数图，不借用整体坍塌后的嵌入。
  obtain ⟨σ, fn, values⟩ := embed.layer_map_l hZF hω model next left layer hbH
  have square x y z (hxy : Rd_entry_d x y σ) (hxz : Rd_entry_d x z k) w :
      Rd_entry_d z w j ↔ Rd_entry_d y w k' := by
    obtain ⟨_, a, b, ha, hab, hyb⟩ := (values x y).mp hxy
    have ea := fk.1.1.2 x a z ((restrict.2 x a).mp ha).2 hxz
    subst a
    exact ⟨fun hzw => (embed.1.1.1.2 z b w hab hzw) ▸ hyb,
      fun hyw => (layer.injection.1.1.2 y b w hyb hyw) ▸ hab⟩
  -- 下一层的全部内部有限图及其空间由原关系边传递，不重建传递高模型。
  have read := owner.rank_read_source_l hZF hBN rankB height omega
  have unions a (ha : M.mem a B) : ∃ p, M.mem p B ∧ M.IsUnionOf p a := by
    obtain ⟨p, hp, code⟩ := owner.theory.algebra.union a (owner.transitive B hBN a ha)
    exact ⟨p, rankB.union_mem_l hZF owner.transitive hBN ha hp code, code⟩
  obtain ⟨read', unions', omega'⟩ := read.map_layer_l hZF hω unions model next embed left layer hbH
  have fixedω := (values ω ω).mpr ⟨omega, omega'⟩
  have cut := (rank.rank_l hZF owner.transitive hΓ hγ hα hBN rankB).2
  obtain ⟨closedB, smallB⟩ := rr_rank_low_l hZF low fk image pred closed small hB cut hBb
  have closed' := (embed.rr_closed_l I hZF hω model next hbH).mp closedB
  have small' := (embed.rr_small_l I hZF hω model next hbH).mp smallB
  -- 有限代数与相对幂集的全称句子覆盖新层的全部新参数。
  let nb : Nonempty {x // M.mem x B} := ⟨⟨ω, omega⟩⟩
  let ng : Nonempty {x // M.mem x Γ'} := ⟨⟨ω, read'.omega_mem⟩⟩
  let ε : Env (rt_model_l B nb) 0 := ⟨Fin.elim0, fun _ => ⟨ω, omega⟩⟩
  have algebra := owner.theory.algebra.rank_l hZF owner.transitive hBN rankB height
  have valid : Formula.satisfies ε (.conj sc_algebra_m sc_power_m) :=
    ⟨(sc_algebra_sat_l (ZF.modelsKP hZF) trans nb ε).mpr algebra, (sc_power_sat_l trans nb ε).mpr power⟩
  obtain ⟨θ, _, truth⟩ := embed.relative_image_l hZF hω model next left layer nb ng hbH
    (.conj sc_algebra_m sc_power_m) (by simp -implicitDefEqProofs [sc_algebra_m, Definitional.Formula.FreeClosed]) ε
  obtain ⟨algebra', power'⟩ := truth.mp valid
  have algebra' := (sc_algebra_sat_l (ZF.modelsKP hZF) layer.transitive ng θ).mp algebra'
  have power' := (sc_power_sat_l layer.transitive ng θ).mp power'
  obtain ⟨a₁, R₁, lowModel⟩ := smdl_membership_l I hZF ⟨ω, read'.omega_mem⟩
  have theory' : Sc_theory_d I ω Γ' R₁ :=
    ⟨fun _ _ _ _ _ _ _ => layer.separation_l hZF hω hX mx theory next root closed' lowModel, algebra'⟩
  -- 同一秩历史先由完整前驱图解释，再沿实际常值嵌入进入新极限。
  obtain ⟨a, ha, hαa⟩ := fk.1.2.2 α hα
  obtain ⟨a', ha', haa⟩ := embed.1.1.2.2 a ha
  have ext : Rf_ext_d I Y S := hq.extensional_l hZF hω mx.1 model (rf_ext_mem_l I hZF.1 hX mx)
  have oldRank := rr_realize_rank_l hZF model ext low fk image pred closed
    ⟨a, ha⟩ ⟨b, fk.1.output_mem_of_pairMember hBb⟩ hαa hBb cut
  let ρ : Env (smdl_structure_l I (R := S) model.2.1) 2 :=
    ⟨Fin.cases ⟨b, fk.1.output_mem_of_pairMember hBb⟩ (fun _ => ⟨a, ha⟩), fun _ => ⟨a, ha⟩⟩
  let η : Env (smdl_structure_l I (R := W) next.2.1) 2 :=
    ⟨Fin.cases ⟨H', embed.1.1.output_mem_of_pairMember hbH⟩ (fun _ => ⟨a', ha'⟩), fun _ => ⟨a', ha'⟩⟩
  have moved := (smap_source_l I hZF hω model next embed (v_sigma_m (.bound 1) .newest)
    (by simp -implicitDefEqProofs) ρ η (Fin.cases hbH (fun _ => haa))).mp oldRank
  exact ⟨J, O, Z, A, p, T, V, r, o, C, W, j, q', k', H', σ, a₁, R₁, system, limit, next, elem, embed, root, certificate, comp,
    layer, fn, graph, square, read', unions', fixedω, lowModel, theory', power',
    closed', small', a, a', hαa, haa, ha', layer.member, moved⟩

end YesMetaZFC.SetTheory.LargeCardinal
