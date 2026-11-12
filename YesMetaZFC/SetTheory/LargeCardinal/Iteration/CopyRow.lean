import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawAgreementRead
import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawCoherence
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.AttemptMember
import YesMetaZFC.Model.SetTheory.Relations.Parity
import YesMetaZFC.Model.SetTheory.Internal.Hereditary
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.Reflection
import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawQualityCopy
import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawSetCopy
import YesMetaZFC.SetTheory.LargeCardinal.Extender.LevelTransfer
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.Coherence
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CopyAnchor
import YesMetaZFC.SetTheory.LargeCardinal.Extender.CommonImage
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.InitialPull

/-! # 工作共同秩段的实际复制方块

原共同层的指定像同时属于两个工作源。恒等限制图覆盖这个像的全部成员；
原有完整方块据此产生两张相等的复合图，供整层有界池搬运直接使用。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ic_working_layer_l {ω c N T d B S a A R σ P π Γ k z κ D η : M.Domain}
    (hω : M.IsOmega ω) (mn : Smdl_d I c N T) (mb : Smem_d I d B S) (ma : Smem_d I a A R)
    (map : Smap_d I ω c d N B σ) (copy : M.IsSetFunctionFromTo I π P A)
    (en : Extensional (smdl_structure_l I (R := T) mn.2.1))
    (w U ξ : (smdl_structure_l I (R := T) mn.2.1).Domain)
    (numbers : Rr_layer_d I ω N T w.val z) (finite : Fs_read_d w U)
    (closed : Rr_closed_d I N T U.val) (hξU : (smdl_structure_l I (R := T) mn.2.1).mem ξ U)
    (carrier : ∀ x, M.mem x Γ ↔ M.mem x N ∧ Rd_entry_d x U.val T)
    (fk : M.IsSetInjectionFromTo I k Γ P)
    (square : ∀ x x' y, Rd_entry_d x x' σ → Rd_entry_d x y k → Rd_entry_d y x' π)
    (hU : Rd_entry_d U.val D σ) (hξ : Rd_entry_d ξ.val κ σ)
    (bt : M.TransitiveSet B) (ta : M.TransitiveSet A) (hw : M.mem ω B)
    (hD : M.mem D A) (rank : Vr_d A η D) :
    ∃ z' k' θ, Rr_layer_d I ω B S ω z' ∧
      (∀ n m, Rd_entry_d n m z' ↔ M.mem n ω ∧ n = m) ∧
      Er_agree_d I ω B S κ z' D A R k' ∧
      (∀ x y, Rd_entry_d x y k' ↔ M.mem x D ∧ x = y) ∧
      (∀ x, M.mem x D ↔ M.mem x B ∧ Rd_entry_d x D S) ∧
      (∀ y, Rd_entry_d y D R ↔ ∃ x, M.mem x D ∧ Rd_entry_d x y k') ∧
      Rr_closed_d I A R D ∧ It_comp_d k π θ ∧ It_comp_d σ k' θ := by
  let N₀ := smdl_structure_l I (R := T) mn.2.1
  let B₀ := smdl_structure_l I (R := S) mb.1.2.1
  have ext : Rf_ext_d I N T := fun x hx y hy same => congrArg Subtype.val
    (en.eq_of_same_members ⟨x, hx⟩ ⟨y, hy⟩ (fun s => same s.val s.property))
  have eb := (rf_ext_mem_l I hZF.1 bt mb).native_l I mb.1.2.1
  have hD' := map.1.1.output_mem_of_pairMember hU
  let w' : B₀.Domain := ⟨ω, hw⟩
  let U' : B₀.Domain := ⟨D, hD'⟩
  let ξ' : B₀.Domain := ⟨κ, map.1.1.output_mem_of_pairMember hξ⟩
  have hww := (numbers.omega_image_mem_l I hZF hω ext mn mb bt map).1
  let ρ : Env N₀ 2 := ⟨Fin.cases U (fun _ => w), fun _ => w⟩
  let τ : Env B₀ 2 := ⟨Fin.cases U' (fun _ => w'), fun _ => w'⟩
  have finite' := (fs_read_sat_l eb τ (.bound 1) .newest).mp
    ((smap_source_l I hZF hω mn mb.1 map (fs_read_m (.bound 1) .newest)
      (by simp -implicitDefEqProofs) ρ τ (Fin.cases hU (fun _ => hww))).mp
        ((fs_read_sat_l en ρ (.bound 1) .newest).mpr finite))
  have closed' := (map.rr_closed_l I hZF hω mn mb.1 hU).mp closed
  have hκD := (map.relation_l I hZF hω mn mb.1 hξ hU).mp hξU
  obtain ⟨z', natural, digits⟩ := rr_layer_mem_l I hZF mb bt hw (hω.transitive (ZF.modelsKP hZF))
  obtain ⟨k', layer, identity⟩ := rr_layer_mem_l I hZF ma ta hD (rank.transitive_l ta hD)
  have dc x : M.mem x D ↔ M.mem x B ∧ Rd_entry_d x D S :=
    ⟨fun hx => ⟨bt D hD' x hx, (mb.2 x D).mpr ⟨bt D hD' x hx, hD', hx⟩⟩,
      fun h => ((mb.2 x D).mp h.2).2.2⟩
  have pred x y (hxy : Rd_entry_d x y k') v :
      Rd_entry_d v y R ↔ ∃ s, Rd_entry_d s x S ∧ Rd_entry_d s v k' := by
    apply (layer.predecessors x y hxy v).trans
    constructor
    · rintro ⟨s, hs, hsv⟩
      exact ⟨s, (mb.2 s x).mpr ⟨bt D hD' s (layer.injection.1.input_mem_of_pairMember hsv),
        bt D hD' x (layer.injection.1.input_mem_of_pairMember hxy), hs⟩, hsv⟩
    · rintro ⟨s, hs, hsv⟩
      exact ⟨s, ((mb.2 s x).mp hs).2.2, hsv⟩
  have ac : Rr_closed_d I A R D := by
    intro x y hx hy hxD sub
    have contained : M.MemberSubset y x := fun s hs => ((ma.2 s x).mp
      (sub s (ta y hy s hs) ((ma.2 s y).mpr ⟨ta y hy s hs, hy, hs⟩))).2.2
    exact (ma.2 y D).mpr ⟨hy, hD, rank.subset_mem_l ta hD ((ma.2 x D).mp hxD).2.2 hy contained⟩
  have agree := er_agree_layer_l I mb.1.2.1 eb w' U' ξ' natural finite' dc layer.injection
    layer.image pred closed' ac hκD
  obtain ⟨θ, fθ, graph⟩ := ZF.exists_compositionFunction hZF I fk.1 copy
  have first : It_comp_d k π θ := ⟨fθ.1.1, fun x y => (graph x y).trans
    ⟨And.right, fun ⟨s, hxs, hsy⟩ => ⟨fk.1.input_mem_of_pairMember hxs, s, hxs, hsy⟩⟩⟩
  refine ⟨z', k', θ, natural, digits, agree, identity, dc, layer.image, ac, first, fθ.1.1, ?_⟩
  intro x y
  constructor
  · intro hxy
    obtain ⟨s, hxs, hsy⟩ := (first.2 x y).mp hxy
    have hx := (carrier x).mp (fk.1.input_mem_of_pairMember hxs)
    obtain ⟨x', _, hxx⟩ := map.1.1.2.2 x hx.1
    have eq := copy.1.2 s x' y (square x x' s hxx hxs) hsy
    have hxD : M.mem x' D := ((mb.2 x' D).mp ((map.relation_l I hZF hω mn mb.1 hxx hU).mp hx.2)).2.2
    exact ⟨x', hxx, (identity x' y).mpr ⟨hxD, eq⟩⟩
  · rintro ⟨x', hxx, hx'y⟩
    obtain ⟨hxD, rfl⟩ := (identity x' y).mp hx'y
    have hx := (carrier x).mpr ⟨map.1.1.input_mem_of_pairMember hxx,
      (map.relation_l I hZF hω mn mb.1 hxx hU).mpr ((mb.2 x' D).mpr ⟨bt D hD' x' hxD, hD', hxD⟩)⟩
    obtain ⟨s, _, hxs⟩ := fk.1.2.2 x hx
    exact (first.2 x x').mpr ⟨s, hxs, square x x' s hxx hxs⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原关系后继到完整工作超幂的一步复制

原所属模型、父模型及给定后继均保持原关系码。所属小秩源的同一扩展器
沿实际初等图读入工作源，再施加于完整工作模型。原系统复制进 j(A)，
同一常值方块随之交换；原后继的良基性与完整源条件由这个实际目标回传。
共同工作秩段、最大强度及所有较低层的一致性由同一大超幂返回。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ic_copy_step_l
    {ω κ L F K₁ K₂ K₃ K₄ A S B T Z V U W α β a d z π σ
      hs P RP bs Ns Ts zs Γ ks Vₚ Ls Js Os Zs Ds ps Vs Ws qs os CP UP js
      D₀ η Dp Bp t₀ l U₁ V₂ Γ₁ k₁ : M.Domain}
    (small : Ep_source_d I ω ω K₁ A S) (cut : Ep_source_d I ω ω K₂ B T)
    (ambient : Ic_model_d hZF ω ω K₃ Z V) (outer : Ic_model_d hZF ω ω K₄ U W)
    (hA : M.mem A Z) (ra : Vr_d Z α A) (hα : M.IsLimitOrdinal α)
    (hB : M.mem B U) (rb : Vr_d U β B) (hβ : M.IsLimitOrdinal β)
    (ha : Smem_d I a A S) (hb : Smem_d I d B T) (hz : Smem_d I z Z V)
    (parent : Smdl_d I hs P RP) (ns : Smdl_d I bs Ns Ts)
    (hπ : Smap_d I ω hs a P A π) (hσ : Smap_d I ω bs d Ns B σ)
    (hNs : (smdl_structure_l I (R := Ts) ns.2.1).Models KP)
    (w ξ ℓ e X₀ δ K₀ R₀ U₀ β₀ A₀ Q₀ B₀ e₀ : (smdl_structure_l I (R := Ts) ns.2.1).Domain)
    (numbers : Rr_layer_d I ω Ns Ts w.val zs)
    (source : Ep_source_d (kp_pair_l hNs) w ξ K₀ X₀ R₀)
    (rank : V_d (kp_pair_l hNs) δ X₀)
    (height : (smdl_structure_l I (R := Ts) ns.2.1).IsLimitOrdinal δ)
    (loc : It_local_d (kp_pair_l hNs) w X₀ R₀ ξ ℓ e)
    (quality : It_owner_d I ω bs ξ.val ℓ.val e.val)
    (hξ : Rd_entry_d ξ.val κ σ) (hℓ : Rd_entry_d ℓ.val L σ) (he : Rd_entry_d e.val F σ)
    (finite : Fs_read_d w U₀) (owner_closed : Rr_closed_d I Ns Ts U₀.val)
    (carrier : ∀ x, M.mem x Γ ↔ M.mem x Ns ∧ Rd_entry_d x U₀.val Ts)
    (hU : Rd_entry_d U₀.val D₀ σ) (hD : M.mem D₀ A)
    (rA : Vr_d A η D₀) (rB : Vr_d B η D₀) (hη : M.IsLimitOrdinal η)
    (agreement : Er_agree_d I ω Ns Ts ξ.val zs Γ P RP ks)
    (square : ∀ x x' y, Rd_entry_d x x' σ → Rd_entry_d x y ks → Rd_entry_d y x' π)
    (parent_image : ∀ y, Rd_entry_d y Vₚ RP ↔ ∃ x, M.mem x Γ ∧ Rd_entry_d x y ks)
    (parent_small : Rr_small_d I P RP Vₚ)
    (hβU : (smdl_structure_l I (R := Ts) ns.2.1).mem β₀ U₀)
    (hβX : (smdl_structure_l I (R := Ts) ns.2.1).mem β₀ X₀)
    (transβ : (smdl_structure_l I (R := Ts) ns.2.1).TransitiveSet β₀)
    (products : ∀ m D : (smdl_structure_l I (R := Ts) ns.2.1).Domain,
      (smdl_structure_l I (R := Ts) ns.2.1).mem m w → Ep_space_d ξ m D →
        ∃ P, (smdl_structure_l I (R := Ts) ns.2.1).mem P U₀ ∧
          (smdl_structure_l I (R := Ts) ns.2.1).IsCartesianProduct (kp_pair_l hNs) P D β₀)
    (pool : Eb_collapse_d w ξ ℓ K₀ X₀ β₀ e A₀ Q₀ B₀ e₀)
    (dc : ∀ x, M.mem x Dp ↔ M.mem x Ns ∧ Rd_entry_d x A₀.val Ts)
    (bc : ∀ x, M.mem x Bp ↔ M.mem x Ns ∧ Rd_entry_d x B₀.val Ts)
    (ft : Fn0_d Bp CP t₀) (present : Er_present_d I ω Ls Ns Ts zs Γ P ks qs e₀.val Dp t₀)
    (prepare : ∀ v : (smdl_structure_l I (R := Ts) ns.2.1).Domain,
      (smdl_structure_l I (R := Ts) ns.2.1).mem v A₀ →
      ∃ α, ∃ m a D f : (smdl_structure_l I (R := Ts) ns.2.1).Domain,
        Ei_d ω Ls α ∧ Rr_finite_d I ω Ls Ns Ts zs α a.val ∧
        (smdl_structure_l I (R := Ts) ns.2.1).mem m w ∧ Fn0_d m ℓ a ∧ Ep_space_d ξ m D ∧
        (smdl_structure_l I (R := Ts) ns.2.1).mem f U₀ ∧ Fn0_d D β₀ f ∧
        KPair_d (smdl_structure_l I (R := Ts) ns.2.1) v a f)
    (length : ∀ x, M.mem x Ls ↔ M.mem x Ns ∧ Rd_entry_d x ℓ.val Ts)
    (raw : Er_graph_d I ω Ls Ns Ts ξ.val ℓ.val e.val zs P RP ks Js Os Zs Ds ps Vs Ws)
    (diagram : Di_system_d Js Os Ds ps Vs Ws) (raw_limit : Di_limit_d Ds ps Vs Ws qs CP UP)
    (original : Smdl_d I os CP UP) (fj : Fn0_d P CP js) (cj : Er_constants_d P qs js)
    (new_common : Ic_common_d I Ns Ts CP UP ℓ.val l U₁ V₂ Γ₁ k₁)
    (restrict : M.IsRestrictionOf I k₁ t₀ Γ₁)
    (endpoint : Rd_entry_d ℓ.val l t₀) (layer : Rd_entry_d U₁ V₂ t₀) :
    ∃ N Rₙ n j Kₙ α' A' S' a' k K', Smem_d I n N Rₙ ∧ It_ultra_d I ω κ L F z n j ∧
      Ic_model_d hZF ω L Kₙ N Rₙ ∧ Rd_entry_d α α' j ∧ Rd_entry_d A A' j ∧ M.IsLimitOrdinal α' ∧
      M.mem A' N ∧ Vr_d N α' A' ∧ Smem_d I a' A' S' ∧ Ep_source_d I ω ω K' A' S' ∧
      Smap_d I ω os a' CP A' k ∧
      (∀ x x' y y', Rd_entry_d x x' π → Rd_entry_d x y js → Rd_entry_d x' y' j → Rd_entry_d y y' k) ∧
      Wf_rel_d CP UP ∧ It_source_d hZF ω os ∧ Ea_agree_d ω κ Z U ∧
      It_local_d I ω U W κ L F ∧ Ex_strength_d I ω κ L U F ∧ Sc_inaccessible_d ω U L ∧
      (∀ x x' E, Rd_entry_d x x' σ → Rd_entry_d x E t₀ → Rd_entry_d E x' k) ∧
      Ic_agree_d I Ns Ts B σ CP UP A' k ℓ.val l L U₁ V₂ Γ₁ k₁ ∧
      ∃ D, M.mem D U ∧ Vr_d U L D ∧ Er_level_d N L D ∧ Sc_rank_size_d I N L ∧
        Es_strength_d U L N ∧ ∀ η, M.mem η L → Ea_agree_d ω η U N := by
  -- 原证书的像给出实际工作扩展器；临界点同时从共同图回收到父模型的像。
  obtain ⟨Kb, owner, loc', strong', card'⟩ := quality.copy_l hZF ns hb hσ hNs cut hξ hℓ he
  have ord := (loc'.ordinals_l (ZF.modelsKP hZF) cut.transitive cut.code).1
  obtain ⟨x, _, hξx⟩ := agreement.injection.1.2.2 ξ.val agreement.critical
  have point := square ξ.val κ x hξ hξx
  have hκA := hπ.1.1.output_mem_of_pairMember point
  have hξU := ((carrier ξ.val).mp agreement.critical).2
  have hκD := ((hb.2 κ D₀).mp ((hσ.relation_l I hZF small.omega ns hb.1 hξ hU).mp hξU)).2.2
  have hD' := hσ.1.1.output_mem_of_pairMember hU
  have hκZ := ambient.source.transitive A hA κ hκA
  have hκU := outer.source.transitive B hB κ owner.cardinal_mem
  obtain ⟨Ka, sa⟩ := small.rebase_l hκA owner.below
    (sc_ordinal_small_l hZF small.omega small.transitive ha small.theory hκA ord)
  obtain ⟨Kz, az⟩ := ambient.rebase_l hZF hκZ owner.below
    (sc_ordinal_small_l hZF small.omega ambient.source.transitive hz ambient.source.theory hκZ ord)
  obtain ⟨u, hu⟩ := outer.source.code
  obtain ⟨Ku, ou⟩ := outer.rebase_l hZF hκU owner.below
    (sc_ordinal_small_l hZF small.omega outer.source.transitive hu outer.source.theory hκU ord)
  have same : Ea_agree_d ω κ A B := fun n D C hn hd hc =>
    (sa.rank_agree_l hZF hD rA hη hκD n D C hn hd hc).symm.trans
      (owner.rank_agree_l hZF hD' rB hη hκD n D C hn hd hc)
  have agree_a := az.source.rank_agree_l hZF hA ra hα hκA
  have agree_b := ou.source.rank_agree_l hZF hB rb hβ owner.cardinal_mem
  have zu : Ea_agree_d ω κ Z U := fun m D C hm hd hc =>
    (agree_a m D C hm hd hc).symm.trans ((same m D C hm hd hc).trans (agree_b m D C hm hd hc))
  have card_u := card'.of_rank_l hZF outer.source.transitive
    (outer.source.algebra_l (ZF.modelsKP hZF)).pair hB rb hβ
  obtain ⟨_, power, cover, inaccessible⟩ := ou.read_l hZF
  obtain ⟨regular, sizes⟩ := inaccessible L card_u
  have above : M.mem ω L := (Formula.satisfies_mem_iff _ _ _).mp
    ((Formula.satisfies_conj_iff _ _ _).mp card_u.2.2).1
  obtain ⟨up, strong, card_full, N, Rₙ, n, j, Kₙ, W', hn, big, next, hW, rW, level, rank_size, exactness, later⟩ :=
    az.rank_apply_l hZFC ou.source (ou.closed.bounded_l I) power cover (regular ω above) sizes
      zu hz hB rb hβ ⟨d, hb⟩ loc' strong' card'
  -- 原小工作源的像由这条大超幂边本身给出，保留其真实相对秩历史。
  have hj := big.elementary_l hZF hz.1 hn.1
  obtain ⟨A', hA', hAA⟩ := hj.1.1.2.2 A hA
  obtain ⟨C, f, hC, hf, cert⟩ := ra
  have hαZ := sc_function_domain_mem_l hZF small.omega az.source.transitive hz az.source.theory hf (cert A hA).2.1
  have ra : Vr_d Z α A := ⟨C, f, hC, hf, cert⟩
  obtain ⟨α', _, hαα⟩ := hj.1.1.2.2 α hαZ
  have ra' := (hj.hierarchy_l hZF small.omega az.source.transitive next.source.transitive hz hn hαα hAA).mp ra
  have hl := (hj.limit_l hZF small.omega az.source.transitive next.source.transitive hz hn hαα).mp hα
  have hw := hj.omega_l I hZF small.omega az.source.transitive next.source.transitive hz hn az.source.omega_mem
  have hwA' := ((hn.2 ω A').mp ((hj.relation_l I hZF small.omega hz.1 hn.1 hw hAA).mp
    ((hz.2 ω A).mpr ⟨az.source.omega_mem, hA, small.omega_mem⟩))).2.2
  obtain ⟨a', S', ha'⟩ := smdl_membership_l I hZF ⟨ω, hwA'⟩
  -- 工作共同图恰以原 U₀ 的实际像为定义域，两张完整复合图一同构造。
  obtain ⟨zt, kt, θ, nt, digits, agree, identity, dc', image', closed', left, right⟩ :=
    ic_working_layer_l hZF small.omega ns hb ha hσ hπ.1.1 hNs.1 w U₀ ξ numbers finite owner_closed hξU
      carrier agreement.injection square hU hξ cut.transitive small.transitive cut.omega_mem hD rA
  have maps : Er_maps_d I ω Ns Ts ξ.val zs ks kt π σ := by
    intro m m' D x x' y y' _ _ _ _ _ hxy hxx hyy
    have eq := hπ.1.1.1.2 y x' y' (square x x' y hxx hxy) hyy
    have hx := (carrier x).mp (agreement.injection.1.input_mem_of_pairMember hxy)
    exact (identity x' y').mpr
      ⟨((hb.2 x' D₀).mp ((hσ.relation_l I hZF small.omega ns hb.1 hxx hU).mp hx.2)).2.2, eq⟩
  have pulled := (it_source_mem_l hZF ha small).pull_l hZF parent ha.1 hπ
  obtain ⟨P₀, Rₚ, _, _, _, mp, core, _⟩ := pulled.objects
  obtain ⟨rfl, rfl⟩ := smdl_unique_l I mp parent
  have owner_local := it_local_short_l I ns.2.1 (kp_pair_l hNs) hNs.1
    (loc.rank_absolute_l hNs source.omega rank height source.code)
  have small_domains := er_domain_small_l I (ω := ω) (N := Ns) (T := Ts) (ξ := ξ.val) (z := zs)
    agreement.injection parent_image parent_small
  have powers (m D : (smdl_structure_l I (R := Ts) ns.2.1).Domain)
      (hm : (smdl_structure_l I (R := Ts) ns.2.1).mem m w) (space : Ep_space_d ξ m D) :
      ∃ B, (smdl_structure_l I (R := Ts) ns.2.1).IsPowerSetOf B D :=
    v_power_exists_l (kp_pair_l hNs) hNs rank (v_subset_mem_l (kp_pair_l hNs) rank source.finite.mem_l
      (fun s hs => ((source.finite_l hNs) s).mpr ⟨m, hm, fn0_function_l hNs ((space s).mp hs)⟩))
  obtain ⟨P', hP', ps'⟩ := power Ku ou.source.finite.mem_l
  have back : Ea_agree_d ω κ U Z := fun m D C hm hd hc => (zu m D C hm hd hc).symm
  have family := (up.measures_l hZF small.omega (ou.source.read_source_l hZF) ou.source.code ou.source.theory
    (sf_finite_power_l hZF small.omega ou.source.transitive ou.source.code ou.source.theory
      (ou.source.finite_l (ZF.modelsKP hZF)) hP' ps')).transfer_l back
  have coherent := (up.coherent_l hZF (ou.source.read_source_l hZF) ou.source.code).transfer_l hZF back
  have saved := big
  obtain ⟨Z₀, V₀, N₀, Rₙ₀, J, O, D, E, p, T₁, V₁, q, c, C₁, W₁, i, e₁,
    mz, mn, system, limit, model, wc, bij, em, _, constants, _, comp⟩ := saved
  obtain ⟨eqZ, eqV⟩ := smdl_unique_l I mz.1 hz.1
  subst Z₀ V₀
  obtain ⟨eqN, eqR⟩ := smdl_unique_l I mn.1 hn.1
  subst N₀ Rₙ₀
  obtain ⟨Jc, Oc, Zc, Dc, pc, Tc, Vc, qc, cc, Cc, Wc, systemc, rawc, limitc, modelc, copied,
    v, k, hv, hk, values, _, commute, wf, ready, ⟨K', small'⟩, _, _, _, τ, ht, nodes, composition⟩ :=
    raw.into_set_l hZFC az.source next.source sa family coherent system limit model hz hn em hj constants comp
      ha ha' hAA (fun m D C hm hd hc => (agree_a m D C hm hd hc).mpr)
      ns hb hσ hNs w ξ ℓ e hξ hℓ he numbers nt digits (owner.read_source_l hZF) owner.theory length owner_local powers
      parent hπ core.ext core.theory core.collection agreement agree (fun x y h => ((identity x y).mp h).2)
      maps small_domains diagram raw_limit original fj cj
  -- 搬运原有界池的全部对象并构造完整目标实现，随后读取同一个集合像因子。
  let Bn := smdl_structure_l I (R := T) hb.1.2.1
  have hBn := hσ.native_models_l hZF small.omega ns hb.1 hNs
  let w' : Bn.Domain := ⟨ω, cut.omega_mem⟩
  let ξ' : Bn.Domain := ⟨κ, owner.cardinal_mem⟩
  let ℓ' : Bn.Domain := ⟨L, hσ.1.1.output_mem_of_pairMember hℓ⟩
  let e' : Bn.Domain := ⟨F, hσ.1.1.output_mem_of_pairMember he⟩
  let U' : Bn.Domain := ⟨D₀, hD'⟩
  obtain ⟨b₀, hb₀, hβ₀⟩ := hσ.1.1.2.2 β₀.val β₀.property
  obtain ⟨a₀, ha₀, hA₀⟩ := hσ.1.1.2.2 A₀.val A₀.property
  obtain ⟨b₁, hb₁, hB₀⟩ := hσ.1.1.2.2 B₀.val B₀.property
  obtain ⟨e₀', he₀', hE₀⟩ := hσ.1.1.2.2 e₀.val e₀.property
  let β' : Bn.Domain := ⟨b₀, hb₀⟩
  let Ap : Bn.Domain := ⟨a₀, ha₀⟩
  let Bp' : Bn.Domain := ⟨b₁, hb₁⟩
  let ep : Bn.Domain := ⟨e₀', he₀'⟩
  obtain ⟨_,_,hℓX,_⟩ := loc
  obtain ⟨Hp, _, support⟩ := (source.sequences_l hNs).1 ℓ hℓX
  obtain ⟨b, _, hβb⟩ := agreement.injection.1.2.2 β₀.val ((carrier β₀.val).mpr ⟨β₀.property, hβU⟩)
  obtain ⟨_, _, ic, _, _, hic, _, cic, _⟩ := copied
  have length' x : M.mem x L ↔ M.mem x B ∧ Rd_entry_d x L T :=
    ⟨fun hx => ⟨cut.transitive L ℓ'.property x hx,
      (hb.2 x L).mpr ⟨cut.transitive L ℓ'.property x hx, ℓ'.property, hx⟩⟩,
      fun h => ((hb.2 x L).mp h.2).2.2⟩
  obtain ⟨Xp, Kp, δp, Qp, H₁, _, _, _, _, _, finite₁, support₁, rank₁, height₁, hK₁, hβ₁,
    pool₁, D₁, B₁, v₁, t₁, _, _, _, _, it₁, present₁, _, ψ, _, first, second⟩ :=
    er_present_copy_l hZF small.omega ns hb.1 hσ hNs parent.2.1 ha.1.2.1
      (core.ext.native_l I parent.2.1) (sa.ext.native_l I ha.1.2.1) hπ.1.1
      U₀ w ξ ℓ e β₀ A₀ B₀ e₀ U' w' ξ' ℓ' e' β' Ap Bp' ep X₀ K₀ δ Q₀ Hp
      hU he hξ hℓ hβ₀ hA₀ hB₀ hE₀ numbers nt finite owner_closed products (source.finite_l hNs)
      support source.finite.mem_l rank height hβX transβ hξU pool owner_local carrier dc'
      agreement.injection agree.injection agreement.predecessors agree.predecessors ha.1 sa.theory image' closed'
      left right hβb length length' raw rawc raw_limit limitc systemc.diagram modelc hic cic
      (fn0_of_function_l (ZF.modelsKP hZF) ht.1.1) nodes dc bc ft present prepare
  have hβD := ((hb.2 b₀ D₀).mp ((hσ.relation_l I hZF small.omega ns hb.1 hβ₀ hU).mp hβU)).2.2
  have hDZ := az.source.transitive A hA D₀ hD
  have rZ := ra.of_rank_l az.source.transitive hA hD rA
  have common := az.source.common_functions_l hZF owner hDZ rZ hD' rB hη hκD hβD
  have hβZ := az.source.transitive D₀ hDZ b₀ hβD
  obtain ⟨G, hG, hβG⟩ := hj.1.1.2.2 b₀ hβZ
  obtain ⟨Hc, hβH, hHG⟩ := (comp.2 b₀ G).mp hβG
  obtain ⟨u₀, a₂, B₂, f₂, D₂, _, ff₂, fc₂, hf₂, pair₂, huH⟩ := constants b₀ Hc hβH
  have transβ' : M.TransitiveSet b₀ := by
    let ρ : Env (smdl_structure_l I (R := Ts) ns.2.1) 1 := ⟨fun _ => β₀, fun _ => β₀⟩
    let ν : Env Bn 1 := ⟨fun _ => β', fun _ => β'⟩
    have tr := (smap_source_l I hZF small.omega ns hb.1 hσ (Formula.isTransitive .newest)
      (by simp -implicitDefEqProofs) ρ ν (fun _ => hβ₀)).mp ((Formula.satisfies_isTransitive_iff ρ .newest).mpr transβ)
    exact (Formula.satisfies_isTransitive_iff (image_env_l (M := Bn) (N := M) Subtype.val ν) .newest).mp
      ((smem_delta_image_l I hb cut.transitive (Formula.isTransitive_delta0 _) ν).mp tr)
  have transG : M.TransitiveSet G := (Formula.satisfies_isTransitive_iff (⟨fun _ => G, fun _ => G⟩ : Env M 1) .newest).mp
    ((smap_delta_l I hZF small.omega az.source.transitive next.source.transitive hz hn hj
      (Formula.isTransitive .newest) (by simp -implicitDefEqProofs) (Formula.isTransitive_delta0 _)
      ⟨fun _ => b₀, fun _ => b₀⟩ ⟨fun _ => G, fun _ => G⟩ (fun _ => hβG)).mp
        ((Formula.satisfies_isTransitive_iff ..).mpr transβ'))
  obtain ⟨_, _, points⟩ := present₁.set_copy_l hZF hb hBn w' ξ' ℓ' Kp Xp β' e' Ap Qp Bp' ep H₁ δp
    az.source owner nt finite₁ support₁ rank₁ height₁ hK₁ hβ₁ common hβZ family system limit wc bij
    (ff₂.function_l az.source.transitive) fc₂ ⟨u₀, B₂, pair₂, hf₂, huH⟩ hHG transG pool₁
    (cut.transitive D₀ hD') digits (fun x y h => ((identity x y).mp h).2) limitc
    (fn0_of_function_l (ZF.modelsKP hZF) hv.1.1) values ft
    (fn0_of_function_l (ZF.modelsKP hZF) ht.1.1) hσ.1.1.1 first second composition
  -- 原完整实现中的两个条目确定新共同层的支撑和秩对象，使用同一个 k。
  have end_image := points ℓ.val L l hℓ endpoint
  have hLA := hk.1.1.output_mem_of_pairMember end_image
  obtain ⟨hwB, rwB⟩ := rb.rank_l hZF outer.source.transitive hB hβ ℓ'.property hW rW
  obtain ⟨hwA, rwA⟩ := ra'.rank_l hZF next.source.transitive hA' hl hLA level.member level.hierarchy
  obtain ⟨U₂, hu₂, hUU⟩ := hσ.1.1.2.2 U₁ new_common.left_rank.2.1
  have moved := ((rr_rank_truth_l I).mp new_common.left_rank).map_l I hZF small.omega ns hb.1 hσ
    (w := Fin.cases U₂ (fun _ : Fin 1 => L))
    (by simp -implicitDefEqProofs) (Fin.cases hUU (fun _ => hℓ))
  have copied_rank := (rr_rank_mem_l I (ZF.modelsKP hZF) hb cut.transitive ℓ'.property hu₂).mp
    ((rr_rank_truth_l I).mpr moved)
  have eq := copied_rank.unique_l hZF cut.transitive hu₂ hwB rwB
  have hUW : Rd_entry_d U₁ W' σ := eq ▸ hUU
  have aligned : Ic_agree_d I Ns Ts B σ CP UP A' k ℓ.val l L U₁ V₂ Γ₁ k₁ :=
    ⟨new_common, cut.transitive, ra'.transitive_l next.source.transitive hA',
      card'.limit_l (ZF.modelsKP hZF) cut.transitive (owner.algebra_l (ZF.modelsKP hZF)).pair,
      ⟨W', hwB, hwA, rwB, rwA, hUW, points U₁ W' V₂ hUW layer⟩, hℓ, end_image,
      fun x x' E hxx hxE => points x x' E hxx ((restrict.2 x E).mp hxE).2⟩
  exact ⟨N, Rₙ, n, j, Kₙ, α', A', S', a', k, K', hn, big, next, hαα, hAA, hl,
    hA', ra', ha', small', hk, commute, wf, ready, zu, up, strong, card_full, points, aligned,
    W', hW, rW, level, rank_size, exactness, later⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原关系模型到工作秩段的实际复制行

原模型只保存其关系码。完整源条件沿实际复制图从工作秩段回拉，
不要求原模型预先具有传递隶属呈示。复制后继保持给定的原关系极限。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}
section
variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Ic_row_d (ω c X A π z Z α : M.Domain) : Prop := ∃ R S V a K K',
  Smdl_d I c X R ∧ Smem_d I a A S ∧ Smem_d I z Z V ∧
    Ep_source_d I ω ω K A S ∧ Ic_model_d hZF ω ω K' Z V ∧
    M.mem A Z ∧ Vr_d Z α A ∧ M.IsLimitOrdinal α ∧ Smap_d I ω c a X A π

def ic_row_m {d} (ω c X A π z Z α : Term d) : Formula 1 d := set[d] ⟪
  ∃ R S V a K K', ⌜smdl_m (𝒞 := kpair_convention_l)⌝ₚ(⌜c⌝ₛ, ⌜X⌝ₛ, R) ∧
    ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(a, ⌜A⌝ₛ, S) ∧
    ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(⌜z⌝ₛ, ⌜Z⌝ₛ, V) ∧
    ⌜ep_source_m⌝ₚ(⌜ω⌝ₛ, ⌜ω⌝ₛ, K, ⌜A⌝ₛ, S) ∧ ⌜ic_model_m⌝ₚ(⌜ω⌝ₛ, ⌜ω⌝ₛ, K', ⌜Z⌝ₛ, V) ∧
    ⌜A⌝ₛ ∈ ⌜Z⌝ₛ ∧ ⌜pn_rank_m⌝ₚ(⌜Z⌝ₛ, ⌜α⌝ₛ, ⌜A⌝ₛ) ∧ ⌜Formula.isLimitOrdinal⌝ₚ(⌜α⌝ₛ) ∧
    ⌜smap_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ, ⌜c⌝ₛ, a, ⌜X⌝ₛ, ⌜A⌝ₛ, ⌜π⌝ₛ)⟫
derive_free_closed ic_row_m

theorem ic_row_sat_l {d} (η : Env M d) (ω c X A π z Z α : Term d) :
    Formula.satisfies η (ic_row_m ω c X A π z Z α) ↔
      Ic_row_d hZF (ω.eval η) (c.eval η) (X.eval η) (A.eval η) (π.eval η) (z.eval η) (Z.eval η) (α.eval η) := by
  simp only [ic_row_m, Ic_row_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_isLimitOrdinal_iff, smdl_sat_l I, smem_sat_l I,
    ep_source_sat_l (ZF.modelsKP hZF), ic_model_sat_l hZF, pn_rank_sat_l (ZF.modelsKP hZF), smap_sat_l I hZF.1,
    Definitional.Term.eval_weaken]; rfl

/-- 同一复制行自动给出原关系源和全部内部数字坐标。 -/
theorem Ic_row_d.source_l {ω c X A π z Z α : M.Domain} (row : Ic_row_d hZF ω c X A π z Z α) :
    It_source_d hZF ω c := by
  obtain ⟨R, S, V, a, K, K', mx, ma, _, small, _, _, _, _, map⟩ := row
  exact (it_source_mem_l hZF ma small).pull_l hZF mx ma.1 map

/-- 只在工作侧重定临界点；原临界点仍是原模型中的对象码。 -/
theorem Ic_row_d.rebase_l {ω c X A π z Z α κ κ' : M.Domain} (row : Ic_row_d hZF ω c X A π z Z α)
    (ord : M.IsOrdinal κ') (below : M.MemberSubset ω κ') (image : Rd_entry_d κ κ' π) :
    ∃ R S V a K K', Smdl_d I c X R ∧ Smem_d I a A S ∧ Smem_d I z Z V ∧
      Ep_source_d I ω κ' K A S ∧ Ic_model_d hZF ω κ' K' Z V ∧
      M.mem A Z ∧ Vr_d Z α A ∧ M.IsLimitOrdinal α ∧ Smap_d I ω c a X A π := by
  obtain ⟨R, S, V, a, _, _, mx, ma, mz, small, ambient, hA, rank, limit, map⟩ := row
  have hκA := map.1.1.output_mem_of_pairMember image
  have hκZ := ambient.source.transitive A hA κ' hκA
  obtain ⟨K, sa⟩ := small.rebase_l hκA below
    (sc_ordinal_small_l hZF small.omega small.transitive ma small.theory hκA ord)
  obtain ⟨K', sz⟩ := ambient.rebase_l hZF hκZ below
    (sc_ordinal_small_l hZF small.omega ambient.source.transitive mz ambient.source.theory hκZ ord)
  exact ⟨R, S, V, a, K, K', mx, ma, mz, sa, sz, hA, rank, limit, map⟩

end
variable (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 给定原源与实际初等图，正规工作外层提供首行。 -/
theorem ic_initial_row_l {ω δ Z α A X R c a S π : M.Domain}
    (source : It_source_d hZF ω c) (mx : Smdl_d I c X R) (ma : Smem_d I a A S)
    (map : Smap_d I ω c a X A π) (above : M.mem ω δ) (regular : M.IsRegularCardinal I δ)
    (outer : V_d I δ Z) (hA : M.mem A Z) (rank : Vr_d Z α A) (limit : M.IsLimitOrdinal α) :
    ∃ z, Ic_row_d hZF ω c X A π z Z α := by
  obtain ⟨K', V, ambient⟩ := ic_regular_model_l hZFC source.omega above regular outer
  obtain ⟨z, mz⟩ := ambient.source.code
  obtain ⟨K, small⟩ := source.image_mem_l hZF mx ma (rank.transitive_l ambient.source.transitive hA) map
  exact ⟨z, R, S, V, a, K, K', mx, ma, mz, small, ambient, hA, rank, limit, map⟩

/-- 同一原关系后继实际生成下一行；原后继的良基性由复制证明。 -/
theorem Ic_row_d.step_l
    {ω c X A π z Z α b H B σ u U β Rₕ Rₓ κ L F o P Rₚ j₀ zs Γ ks
      Vₚ Ls Js Os Zs Ds ps Vs Ws qs D₀ η Dp Bp t₀ l U₁ V₂ Γ₁ k₁ : M.Domain}
    (row : Ic_row_d hZF ω c X A π z Z α) (own : Ic_row_d hZF ω b H B σ u U β)
    (mx : Smdl_d I c X Rₓ) (mh : Smdl_d I b H Rₕ)
    (hN : (smdl_structure_l I (R := Rₕ) mh.2.1).Models KP)
    (w ξ ℓ e X₀ δ K₀ R₀ U₀ β₀ A₀ Q₀ B₀ e₀ : (smdl_structure_l I (R := Rₕ) mh.2.1).Domain)
    (numbers : Rr_layer_d I ω H Rₕ w.val zs) (source : Ep_source_d (kp_pair_l hN) w ξ K₀ X₀ R₀)
    (rank : V_d (kp_pair_l hN) δ X₀) (height : (smdl_structure_l I (R := Rₕ) mh.2.1).IsLimitOrdinal δ)
    (loc : It_local_d (kp_pair_l hN) w X₀ R₀ ξ ℓ e)
    (quality : It_owner_d I ω b ξ.val ℓ.val e.val)
    (hξ : Rd_entry_d ξ.val κ σ) (hℓ : Rd_entry_d ℓ.val L σ) (he : Rd_entry_d e.val F σ)
    (finite : Fs_read_d w U₀) (owner_closed : Rr_closed_d I H Rₕ U₀.val)
    (carrier : ∀ x, M.mem x Γ ↔ M.mem x H ∧ Rd_entry_d x U₀.val Rₕ)
    (hU : Rd_entry_d U₀.val D₀ σ) (hD : M.mem D₀ A)
    (rA : Vr_d A η D₀) (rB : Vr_d B η D₀) (hη : M.IsLimitOrdinal η)
    (agreement : Er_agree_d I ω H Rₕ ξ.val zs Γ X Rₓ ks)
    (square : ∀ x x' y, Rd_entry_d x x' σ → Rd_entry_d x y ks → Rd_entry_d y x' π)
    (parent_image : ∀ y, Rd_entry_d y Vₚ Rₓ ↔ ∃ x, M.mem x Γ ∧ Rd_entry_d x y ks)
    (parent_small : Rr_small_d I X Rₓ Vₚ)
    (hβU : (smdl_structure_l I (R := Rₕ) mh.2.1).mem β₀ U₀)
    (hβX : (smdl_structure_l I (R := Rₕ) mh.2.1).mem β₀ X₀)
    (transβ : (smdl_structure_l I (R := Rₕ) mh.2.1).TransitiveSet β₀)
    (products : ∀ m D : (smdl_structure_l I (R := Rₕ) mh.2.1).Domain,
      (smdl_structure_l I (R := Rₕ) mh.2.1).mem m w → Ep_space_d ξ m D →
        ∃ P, (smdl_structure_l I (R := Rₕ) mh.2.1).mem P U₀ ∧
          (smdl_structure_l I (R := Rₕ) mh.2.1).IsCartesianProduct (kp_pair_l hN) P D β₀)
    (pool : Eb_collapse_d w ξ ℓ K₀ X₀ β₀ e A₀ Q₀ B₀ e₀)
    (dc : ∀ x, M.mem x Dp ↔ M.mem x H ∧ Rd_entry_d x A₀.val Rₕ)
    (bc : ∀ x, M.mem x Bp ↔ M.mem x H ∧ Rd_entry_d x B₀.val Rₕ)
    (ft : Fn0_d Bp P t₀) (present : Er_present_d I ω Ls H Rₕ zs Γ X ks qs e₀.val Dp t₀)
    (prepare : ∀ v : (smdl_structure_l I (R := Rₕ) mh.2.1).Domain,
      (smdl_structure_l I (R := Rₕ) mh.2.1).mem v A₀ →
      ∃ α, ∃ m a D f : (smdl_structure_l I (R := Rₕ) mh.2.1).Domain,
        Ei_d ω Ls α ∧ Rr_finite_d I ω Ls H Rₕ zs α a.val ∧
        (smdl_structure_l I (R := Rₕ) mh.2.1).mem m w ∧ Fn0_d m ℓ a ∧ Ep_space_d ξ m D ∧
        (smdl_structure_l I (R := Rₕ) mh.2.1).mem f U₀ ∧ Fn0_d D β₀ f ∧
        KPair_d (smdl_structure_l I (R := Rₕ) mh.2.1) v a f)
    (length : ∀ x, M.mem x Ls ↔ M.mem x H ∧ Rd_entry_d x ℓ.val Rₕ)
    (raw : Er_graph_d I ω Ls H Rₕ ξ.val ℓ.val e.val zs X Rₓ ks Js Os Zs Ds ps Vs Ws)
    (diagram : Di_system_d Js Os Ds ps Vs Ws) (limit : Di_limit_d Ds ps Vs Ws qs P Rₚ)
    (original : Smdl_d I o P Rₚ) (fj : Fn0_d X P j₀) (cj : Er_constants_d X qs j₀)
    (new_common : Ic_common_d I H Rₕ P Rₚ ℓ.val l U₁ V₂ Γ₁ k₁)
    (restrict : M.IsRestrictionOf I k₁ t₀ Γ₁)
    (endpoint : Rd_entry_d ℓ.val l t₀) (layer : Rd_entry_d U₁ V₂ t₀) :
    ∃ N n A' α' j k, Ic_row_d hZF ω o P A' k n N α' ∧
      Rd_entry_d α α' j ∧ Rd_entry_d A A' j ∧ It_ultra_d I ω κ L F z n j ∧
      (∀ x x' y y', Rd_entry_d x x' π → Rd_entry_d x y j₀ → Rd_entry_d x' y' j → Rd_entry_d y y' k) ∧
      Wf_rel_d P Rₚ ∧ It_source_d hZF ω o ∧ Ea_agree_d ω κ Z U ∧
      (∀ x x' E, Rd_entry_d x x' σ → Rd_entry_d x E t₀ → Rd_entry_d E x' k) ∧
      Ic_agree_d I H Rₕ B σ P Rₚ A' k ℓ.val l L U₁ V₂ Γ₁ k₁ ∧
      ∃ Rᵤ, Smem_d I u U Rᵤ ∧ It_local_d I ω U Rᵤ κ L F ∧
        Ex_strength_d I ω κ L U F ∧ Sc_inaccessible_d ω U L ∧
        ∃ D, M.mem D U ∧ Vr_d U L D ∧ Er_level_d N L D ∧ Sc_rank_size_d I N L ∧
          Es_strength_d U L N ∧ ∀ η, M.mem η L → Ea_agree_d ω η U N := by
  obtain ⟨R, S, V, a, _, _, mx₀, ma, mz, small, ambient, hA, ra, hα, hp⟩ := row
  obtain ⟨R', T, W, d, _, _, mh₀, mb, mu, cut, outer, hB, rb, hβ, hs⟩ := own
  obtain ⟨_, rfl⟩ := smdl_unique_l I mx₀ mx
  obtain ⟨_, rfl⟩ := smdl_unique_l I mh₀ mh
  obtain ⟨N, Rₙ, n, j, Kₙ, α', A', S', a', k, K', mn, big, next, hαα, hAA, hl,
    hA', ra', ma', small', hk, commute, wf, ready, zu, up, strong, card_full, points, aligned, shared⟩ :=
    ic_copy_step_l hZFC small cut ambient outer hA ra hα hB rb hβ ma mb mz mx mh hp hs hN
      w ξ ℓ e X₀ δ K₀ R₀ U₀ β₀ A₀ Q₀ B₀ e₀ numbers source rank height loc quality hξ hℓ he
      finite owner_closed carrier hU hD rA rB hη agreement square parent_image parent_small hβU hβX transβ products
      pool dc bc ft present prepare length raw diagram limit original fj cj new_common restrict endpoint layer
  obtain ⟨Kn, full⟩ := next.rebase_l hZF next.source.omega_mem (fun _ h => h)
    (next.source.cardinal_small.mono_mem_l I mn next.source.omega_mem next.source.below)
  exact ⟨N, n, A', α', j, k, ⟨Rₚ, S', Rₙ, a', K', Kn, original, ma', mn, small', full, hA', ra', hl, hk⟩,
    hαα, hAA, big, commute, wf, ready, zu, points, aligned, W, mu, up, strong, card_full, shared⟩

end YesMetaZFC.SetTheory.LargeCardinal
