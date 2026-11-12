import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawCopyClass
import YesMetaZFC.Model.SetTheory.Relations.CrossProjection
import YesMetaZFC.Model.SetTheory.ReducedPower.RelationProjection
import YesMetaZFC.Model.SetTheory.Relations.CollectCode
import YesMetaZFC.SetTheory.LargeCardinal.Extender.Ultrapower
import YesMetaZFC.Model.SetTheory.DirectedSystem.Relative

/-! # 对象码定义域上的原扩展器重排

原测度协调律先作用于所属模型中的实际截集，随后沿满坐标读取其逆像。
背景投影与所属投影使用同一函数，因而所得推前方程可直接送入原关系
分量的完整内部初等过渡。所属模型只需 KP；投影所在的共同层只提供
当前定义域乘积和子集闭包，不再调用该层的全赋值空间与源理论。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal FilterZF
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem er_cross_push_l {N T D E t t₀ t₁ P Q U V : M.Domain}
    (nx : ∃ x, M.mem x N) (hN : (smdl_structure_l I (R := T) nx).Models KP)
    (w ξ ℓ f m n r a b u v d e p : (smdl_structure_l I (R := T) nx).Domain)
    (hm : (smdl_structure_l I (R := T) nx).mem m w)
    (hn : (smdl_structure_l I (R := T) nx).mem n w)
    (fr : Fn0_d m n r) (fa : Fn0_d n ℓ a) (comp : Cp0_d m n ℓ r a b)
    (hav : Rd_entry_d a v f) (hbu : Rd_entry_d b u f)
    (coherent : Es_coherent_d (kp_pair_l hN) w ξ ℓ f)
    (ds : Ep_space_d ξ m d) (es : Ep_space_d ξ n e)
    (bounded₀ : ∀ A, (smdl_structure_l I (R := T) nx).mem A u → (smdl_structure_l I (R := T) nx).MemberSubset A d)
    (bounded₁ : ∀ A, (smdl_structure_l I (R := T) nx).mem A v → (smdl_structure_l I (R := T) nx).MemberSubset A e)
    (projection : ∀ s q, Rd_entry_d s q p ↔ (smdl_structure_l I (R := T) nx).mem s e ∧ Cp0_d m n ξ r s q)
    (dc : ∀ x, M.mem x D ↔ M.mem x N ∧ Rd_entry_d x d.val T)
    (ec : ∀ x, M.mem x E ↔ M.mem x N ∧ Rd_entry_d x e.val T)
    (fd : M.IsSetFunctionFromTo I t₀ D N) (fe : M.IsSetFunctionFromTo I t₁ E N)
    (id₀ : ∀ x y, Rd_entry_d x y t₀ ↔ M.mem x D ∧ x = y)
    (id₁ : ∀ x y, Rd_entry_d x y t₁ ↔ M.mem x E ∧ x = y)
    (ft : Fn0_d E D t)
    (graph : ∀ s q : (smdl_structure_l I (R := T) nx).Domain, Rd_entry_d s.val q.val t ↔ Rd_entry_d s q p)
    (source : Rt_source_d I N T D t₀ P) (target : Rt_source_d I N T E t₁ Q)
    (su : ∀ A, M.mem A U ↔ ∃ B, M.mem B N ∧ Rd_entry_d B u.val T ∧ Rt_trace_d I D t₀ T B A)
    (sv : ∀ A, M.mem A V ↔ ∃ B, M.mem B N ∧ Rd_entry_d B v.val T ∧ Rt_trace_d I E t₁ T B A) :
    Push_d D E P Q U V t := by
  let N₀ := smdl_structure_l I (R := T) nx
  have onto₀ x (hx : M.mem x N) (hxd : Rd_entry_d x d.val T) : ∃ s, M.mem s D ∧ Rd_entry_d s x t₀ :=
    ⟨x, (dc x).mpr ⟨hx, hxd⟩, (id₀ x x).mpr ⟨(dc x).mpr ⟨hx, hxd⟩, rfl⟩⟩
  have onto₁ x (hx : M.mem x N) (hxe : Rd_entry_d x e.val T) : ∃ s, M.mem s E ∧ Rd_entry_d s x t₁ :=
    ⟨x, (ec x).mpr ⟨hx, hxe⟩, (id₁ x x).mpr ⟨(ec x).mpr ⟨hx, hxe⟩, rfl⟩⟩
  have domain s x (hsx : Rd_entry_d s x t₀) : Rd_entry_d x d.val T :=
    ((id₀ s x).mp hsx).2 ▸ ((dc s).mp ((id₀ s x).mp hsx).1).2
  refine ⟨ft, fun A hA => ?_⟩
  obtain ⟨C, hC, trace⟩ := (source A).mp hA
  obtain ⟨A', cut⟩ := KP.intersection_exists_d hN d (⟨C, hC⟩ : N₀.Domain)
  have sub : N₀.MemberSubset A' d := fun x hx => ((cut x).mp hx).1
  have trA : Rt_trace_d I D t₀ T A'.val A := fun s => (trace s).trans
    (and_congr_right fun _ => exists_congr fun x => and_congr_right fun hsx =>
      ((cut ⟨x, fd.output_mem_of_pairMember hsx⟩).trans (and_iff_right (domain s x hsx))).symm)
  obtain ⟨B', pull, measure⟩ := coherent m n r a b u v A' hm hn fr fa comp hav hbu
    (fun x hx => (ds x).mp (sub x hx))
  have sub' : N₀.MemberSubset B' e := fun x hx => (es x).mpr ((pull x).mp hx).1
  obtain ⟨B, trB⟩ := rt_trace_exists_l I hZF E t₁ T B'.val
  have hB := (target B).mpr ⟨B'.val, B'.property, trB⟩
  have readA := rt_measure_read_l I nx hN.1 d u A' fd onto₀ sub trA bounded₀ su
  have readB := rt_measure_read_l I nx hN.1 e v B' fe onto₁ sub' trB bounded₁ sv
  refine ⟨B, hB, ?_, readB.trans (measure.trans readA.symm)⟩
  intro s
  by_cases hs : M.mem s E
  · let s' : N₀.Domain := ⟨s, ((ec s).mp hs).1⟩
    have hse : N₀.mem s' e := ((ec s).mp hs).2
    apply (trB.value_l I fe ((id₁ s s).mpr ⟨hs, rfl⟩)).trans ((pull s').trans ?_)
    constructor
    · rintro ⟨_, q, hq, comp⟩
      have hqd := (dc q.val).mpr ⟨q.property, sub q hq⟩
      exact ⟨hs, q.val, (trA.value_l I fd ((id₀ q.val q.val).mpr ⟨hqd, rfl⟩)).mpr hq,
        (graph s' q).mpr ((projection s' q).mpr ⟨hse, comp⟩)⟩
    · rintro ⟨_, q, hq, hsq⟩
      have hqd := (ft.bound_l hsq).2
      let q' : N₀.Domain := ⟨q, ((dc q).mp hqd).1⟩
      exact ⟨(es s').mp hse, q', (trA.value_l I fd ((id₀ q q).mpr ⟨hqd, rfl⟩)).mp hq,
        ((projection s' q').mp ((graph s' q').mp hsq)).2⟩
  · exact iff_of_false (fun h => hs ((trB s).mp h).1) (fun h => hs h.1)

section Projection
variable (hZFC : M.Models ZFC)
local notation "hZ" => ZFC.models_zf_l hZFC
local notation "J" => kp_pair_l (ZF.modelsKP hZ)

/-- 原支撑重排实际生成同一投影、两个测度间的推前及完整初等过渡。 -/
theorem It_local_d.raw_projection_l {ω c X R c' Y S q Γ H k N T z L m n r a b
    D E i₀ i₁ t₀ t₁ d₀ e₀ P Q V₀ V₁ G₀ G₁ o₀ o₁ p₀ p₁ C₀ C₁ S₀ S₁ : M.Domain}
    (hω : M.IsOmega ω) (ex : Rf_ext_d J X R) (mx : Smdl_d J c X R)
    (theory : Sc_theory_d J ω X R) (collection : Sc_collection_d J ω X R)
    (model : Smdl_d J c' Y S) (hq : Smap_d J ω c c' X Y q)
    (nx : ∃ x, M.mem x N) (hN : (smdl_structure_l J (R := T) nx).Models KP)
    (U w ξ ℓ f m' n' a' b' d e u v : (smdl_structure_l J (R := T) nx).Domain)
    (numbers : Rr_layer_d J ω N T w.val z)
    (trans : (smdl_structure_l J (R := T) nx).TransitiveSet U)
    (product : ∃ B, (smdl_structure_l J (R := T) nx).mem B U ∧
      (smdl_structure_l J (R := T) nx).IsCartesianProduct (kp_pair_l hN) B e d)
    (carrier : ∀ x, M.mem x Γ ↔ M.mem x N ∧ Rd_entry_d x U.val T)
    (ownerClosed : Rr_closed_d J N T U.val)
    (fk : M.IsSetInjectionFromTo J k Γ Y)
    (image : ∀ y, Rd_entry_d y H S ↔ ∃ x, M.mem x Γ ∧ Rd_entry_d x y k)
    (pred : ∀ x y, Rd_entry_d x y k → ∀ v, Rd_entry_d v y S ↔ ∃ s, Rd_entry_d s x T ∧ Rd_entry_d s v k)
    (small : Rr_small_d J Y S H)
    (hd : (smdl_structure_l J (R := T) nx).mem d U) (he : (smdl_structure_l J (R := T) nx).mem e U)
    (length : ∀ x, M.mem x L ↔ M.mem x N ∧ Rd_entry_d x ℓ.val T)
    (hm : M.mem m ω) (hn : M.mem n ω) (fr : Fn0_d m n r) (factor : Cp0_d m n L r a b)
    (hmm : Rd_entry_d m m'.val z) (hnn : Rd_entry_d n n'.val z)
    (fa : Fn0_d n' ℓ a') (fb : Fn0_d m' ℓ b')
    (ga : Rc_graph_d J N T z a'.val a) (gb : Rc_graph_d J N T z b'.val b)
    (ds : Ep_space_d ξ m' d) (es : Ep_space_d ξ n' e) (hav : Rd_entry_d a' v f) (hbu : Rd_entry_d b' u f)
    (dc : ∀ x, M.mem x D ↔ M.mem x N ∧ Rd_entry_d x d.val T)
    (ec : ∀ x, M.mem x E ↔ M.mem x N ∧ Rd_entry_d x e.val T)
    (fi₀ : M.IsSetFunctionFromTo J i₀ D N) (fi₁ : M.IsSetFunctionFromTo J i₁ E N)
    (id₀ : ∀ x y, Rd_entry_d x y i₀ ↔ M.mem x D ∧ x = y)
    (id₁ : ∀ x y, Rd_entry_d x y i₁ ↔ M.mem x E ∧ x = y)
    (rt₀ : M.IsRestrictionOf J t₀ k D) (rt₁ : M.IsRestrictionOf J t₁ k E)
    (ft₀ : Fn0_d D Y t₀) (ft₁ : Fn0_d E Y t₁) (hdd : Rd_entry_d d.val d₀ k) (hee : Rd_entry_d e.val e₀ k)
    (ownerP : Rt_source_d J N T D i₀ P) (ownerQ : Rt_source_d J N T E i₁ Q)
    (sourceP : Rt_source_d J Y S D t₀ P) (sourceQ : Rt_source_d J Y S E t₁ Q)
    (ultra₀ : Rel_ultra_d D P V₀) (ultra₁ : Rel_ultra_d E Q V₁)
    (su : ∀ A, M.mem A V₀ ↔ ∃ B, M.mem B N ∧ Rd_entry_d B u.val T ∧ Rt_trace_d J D i₀ T B A)
    (sv : ∀ A, M.mem A V₁ ↔ ∃ B, M.mem B N ∧ Rd_entry_d B v.val T ∧ Rt_trace_d J E i₁ T B A)
    (family₀ : Rc_family_d J Y S D d₀ t₀ G₀) (family₁ : Rc_family_d J Y S E e₀ t₁ G₁)
    (quotient₀ : Rp_model_d J D Y V₀ S o₀ G₀ p₀ C₀ S₀) (quotient₁ : Rp_model_d J E Y V₁ S o₁ G₁ p₁ C₁ S₁)
    (loc : It_local_d J w.val N T ξ.val ℓ.val f.val) :
    ∃ r' p : (smdl_structure_l J (R := T) nx).Domain,
      Fn0_d m' n' r' ∧ Cp0_d m' n' ℓ r' a' b' ∧ (smdl_structure_l J (R := T) nx).mem p U ∧ Fn0_d e d p ∧
      (∀ s t, Rd_entry_d s t p ↔ (smdl_structure_l J (R := T) nx).mem s e ∧ Cp0_d m' n' ξ r' s t) ∧
      ∃ t K j, Fn0_d E D t ∧
        (∀ s q : (smdl_structure_l J (R := T) nx).Domain, Rd_entry_d s.val q.val t ↔ Rd_entry_d s q p) ∧
        Push_d D E P Q V₀ V₁ t ∧ M.IsSetFunctionFromTo J K G₀ G₁ ∧
        (∀ f g, Rd_entry_d f g K ↔ M.mem f G₀ ∧ M.mem g G₁ ∧ Cp0_d E D Y t f g) ∧
        Smap_d J ω o₀ o₁ C₀ C₁ j ∧ Rp_lift_d J K p₀ p₁ j ∧
        ∃ j₀ j₁, Smap_d J ω c' o₀ Y C₀ j₀ ∧ Smap_d J ω c' o₁ Y C₁ j₁ ∧
          (∀ x B, Rd_entry_d x B j₀ ↔ M.mem x Y ∧ ∃ g, M.mem g G₀ ∧ Rs_const_d D x g ∧ Rd_entry_d g B p₀) ∧
          (∀ x B, Rd_entry_d x B j₁ ↔ M.mem x Y ∧ ∃ g, M.mem g G₁ ∧ Rs_const_d E x g ∧ Rd_entry_d g B p₁) ∧
          ∀ x B C, Rd_entry_d x B j₀ → (Rd_entry_d B C j ↔ Rd_entry_d x C j₁) := by
  let N₀ := smdl_structure_l J (R := T) nx
  have actual := loc.read_l J _ (kp_pair_l hN) hN.1 w ξ ℓ f
  have hm' : N₀.mem m' w := (numbers.image m'.val).mpr ⟨m, hm, hmm⟩
  have hn' : N₀.mem n' w := (numbers.image n'.val).mpr ⟨n, hn, hnn⟩
  obtain ⟨r', fr', factor'⟩ := numbers.factor_l hZ hN.1 (KP.exists_pair hN) (KP.exists_union hN) hω (fun _ h => h) hm
    m' n' ℓ a' b' hmm hnn length fr factor fb ga gb
  -- KP 构造同一坐标投影；其图是已有乘积的子集，故由共同层闭包回收。
  obtain ⟨p, fp, projection⟩ := cp0_projection_l hN fr' es ds
  obtain ⟨B, hB, product⟩ := product
  have hp : N₀.mem p U := ownerClosed B.val p.val B.property p.property hB
    (fun x hx hxp => (product ⟨x, hx⟩).mpr (fp.1 ⟨x, hx⟩ hxp))
  have ext : Rf_ext_d J Y S := hq.extensional_l hZ hω mx model ex
  have collect := (sc_collection_iff_l J hZ hω mx model
    (ex.native_l J mx.2.1) (ext.native_l J model.2.1) hq).mp collection
  have ey := ext.native_l J model.2.1
  let d' : (smdl_structure_l J (R := S) model.2.1).Domain := ⟨d₀, fk.1.output_mem_of_pairMember hdd⟩
  let e' : (smdl_structure_l J (R := S) model.2.1).Domain := ⟨e₀, fk.1.output_mem_of_pairMember hee⟩
  obtain ⟨t, ft, graph, p', _, fp', comm⟩ := rr_cross_projection_l hZ nx model.2.1 hN.1 ey U d e p
    trans carrier fk pred hp fp dc ec rt₀ rt₁ d' e' hdd hee
  have push := er_cross_push_l hZ nx hN w ξ ℓ f m' n' r' a' b' u v d e p hm' hn' fr' fa factor' hav hbu
    actual.coherent ds es (actual.measures.at_l hN.1 hbu fb ds).1.1 (actual.measures.at_l hN.1 hav fa es).1.1
    projection dc ec fi₀ fi₁ id₀ id₁ ft graph ownerP ownerQ su sv
  have domain₀ s x (hsx : Rd_entry_d s x t₀) := (pred d.val d₀ hdd x).mpr
    ⟨s, ((dc s).mp ((rt₀.2 s x).mp hsx).1).2, ((rt₀.2 s x).mp hsx).2⟩
  have domain₁ s x (hsx : Rd_entry_d s x t₁) := (pred e.val e₀ hee x).mpr
    ⟨s, ((ec s).mp ((rt₁.2 s x).mp hsx).1).2, ((rt₁.2 s x).mp hsx).2⟩
  obtain ⟨μ₀, ε₀, small₀⟩ := (small d₀ d'.property ((image d₀).mpr ⟨d.val, (carrier d.val).mpr ⟨d.property, hd⟩, hdd⟩)).index_l J model.2.1 d'
  obtain ⟨μ₁, ε₁, small₁⟩ := (small e₀ e'.property ((image e₀).mpr ⟨e.val, (carrier e.val).mpr ⟨e.property, he⟩, hee⟩)).index_l J model.2.1 e'
  have g₀ := (rc_family_native_l J model.2.1 ey d' ft₀).mp family₀
  have g₁ := (rc_family_native_l J model.2.1 ey e' ft₁).mp family₁
  obtain ⟨K, j, fK, graphK, embed, lift⟩ := rc_projection_embedding_l hZFC hω ex mx theory model hq
    d' e' p' (collect model.2.1 d' μ₀ ε₀ small₀) (collect model.2.1 e' μ₁ ε₁ small₁) fp' ft₀ ft₁ domain₀ domain₁ comm sourceP sourceQ ultra₀ ultra₁ push g₀ g₁ quotient₀ quotient₁
  obtain ⟨j₀, sj₀, constants₀⟩ := rc_constant_embedding_l hZ hω model ext (theory.map_l J hZ hω mx model hq)
    d' (collect model.2.1 d' μ₀ ε₀ small₀) ft₀ domain₀ sourceP ultra₀ g₀ quotient₀
  obtain ⟨j₁, sj₁, constants₁⟩ := rc_constant_embedding_l hZ hω model ext (theory.map_l J hZ hω mx model hq)
    e' (collect model.2.1 e' μ₁ ε₁ small₁) ft₁ domain₁ sourceQ ultra₁ g₁ quotient₁
  exact ⟨r', p, fr', factor', hp, fp, projection, t, K, j, ft, graph, push, fK, graphK, embed, lift,
    j₀, j₁, sj₀, sj₁, constants₀, constants₁,
    rs_projection_constant_l J quotient₀.map quotient₁.map ft fK (fun f g h => ((graphK f g).mp h).2.2)
      embed.1.1 lift sj₁.1.1 constants₀ constants₁⟩

end Projection
end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原对象码投影的恒等与复合律

单射支撑使坐标重排唯一，因而支撑方程决定重排的恒等和复合。
这些方程经原函数展开图传到实际坐标图，再沿同一代表族下降到商。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

private theorem er_factor_identity_l {n L a q : M.Domain}
    (fa : Fn0_d n L a) (fq : Fn0_d n n q)
    (inj : ∀ i j x, Rd_entry_d i x a → Rd_entry_d j x a → i = j)
    (factor : Cp0_d n n L q a a) : ∀ i j, Rd_entry_d i j q ↔ M.mem i n ∧ i = j := by
  have fixed i j (hij : Rd_entry_d i j q) : i = j := by
    obtain ⟨x, _, hjx⟩ := fa.2.1 j (fq.bound_l hij).2
    exact inj i j x ((factor.value_l fq fa hij).mpr hjx) hjx
  intro i j
  exact ⟨fun h => ⟨(fq.bound_l h).1, fixed i j h⟩, fun ⟨hi, eq⟩ => by
    obtain ⟨k, _, hik⟩ := fq.2.1 i hi
    exact ((fixed i k hik).symm.trans eq) ▸ hik⟩

theorem er_projection_identity_l {N T D t X V G r C K j : M.Domain}
    (nx : ∃ x, M.mem x N)
    (n ξ L a q d p : (smdl_structure_l I (R := T) nx).Domain)
    (fa : Fn0_d n L a) (fq : Fn0_d n n q)
    (inj : ∀ i j x, Rd_entry_d i x a → Rd_entry_d j x a → i = j) (factor : Cp0_d n n L q a a)
    (space : ∀ f, (smdl_structure_l I (R := T) nx).mem f d → Fn0_d n ξ f)
    (fp : Fn0_d d d p)
    (projection : ∀ f g, Rd_entry_d f g p ↔ (smdl_structure_l I (R := T) nx).mem f d ∧ Cp0_d n n ξ q f g)
    (dc : ∀ x, M.mem x D ↔ M.mem x N ∧ M.PairMember I x d.val T) (ft : Fn0_d D D t)
    (graph : ∀ x y : (smdl_structure_l I (R := T) nx).Domain, Rd_entry_d x.val y.val t ↔ Rd_entry_d x y p)
    (model : Rp_map_d I D X V G r C) (fj : M.IsSetFunctionFromTo I j C C)
    (map : ∀ f g, M.PairMember I f g K ↔ M.mem f G ∧ M.mem g G ∧ Cp0_d D D X t f g)
    (lift : Rp_lift_d I K r r j) :
    ∀ B A, M.PairMember I B A j ↔ M.mem B C ∧ B = A := by
  have iq := er_factor_identity_l fa fq inj factor
  have ip := cp0_projection_id_l space fp iq projection
  have it := smdl_graph_identity_l I nx d p dc ft graph ip
  exact rs_projection_id_l I model fj it map lift

theorem er_projection_composition_l
    {N T D₀ D₁ D₂ t₀₁ t₁₂ t₀₂ X V₀ V₁ V₂ G₀ G₁ G₂ p₀ p₁ p₂ C₀ C₁ C₂ K₀₁ K₁₂ K₀₂ j₀₁ j₁₂ j₀₂ : M.Domain}
    (nx : ∃ x, M.mem x N) (hN : (smdl_structure_l I (R := T) nx).Models KP)
    (m₀ m₁ m₂ ξ L a₀ a₁ a₂ q₀₁ q₁₂ q₀₂ d₀ d₁ d₂ r₀₁ r₁₂ r₀₂ : (smdl_structure_l I (R := T) nx).Domain)
    (fq₀₁ : Fn0_d m₀ m₁ q₀₁) (fq₁₂ : Fn0_d m₁ m₂ q₁₂) (fq₀₂ : Fn0_d m₀ m₂ q₀₂)
    (fa : Fn0_d m₂ L a₂) (inj : ∀ i j x, Rd_entry_d i x a₂ → Rd_entry_d j x a₂ → i = j)
    (f₀₁ : Cp0_d m₀ m₁ L q₀₁ a₁ a₀) (f₁₂ : Cp0_d m₁ m₂ L q₁₂ a₂ a₁) (f₀₂ : Cp0_d m₀ m₂ L q₀₂ a₂ a₀)
    (space : ∀ f, (smdl_structure_l I (R := T) nx).mem f d₂ → Fn0_d m₂ ξ f)
    (fr₀₁ : Fn0_d d₁ d₀ r₀₁) (fr₁₂ : Fn0_d d₂ d₁ r₁₂) (fr₀₂ : Fn0_d d₂ d₀ r₀₂)
    (r₀₁s : ∀ f g, Rd_entry_d f g r₀₁ → Cp0_d m₀ m₁ ξ q₀₁ f g)
    (r₁₂s : ∀ f g, Rd_entry_d f g r₁₂ → Cp0_d m₁ m₂ ξ q₁₂ f g)
    (r₀₂s : ∀ f g, (smdl_structure_l I (R := T) nx).mem f d₂ → Cp0_d m₀ m₂ ξ q₀₂ f g → Rd_entry_d f g r₀₂)
    (dc₀ : ∀ x, M.mem x D₀ ↔ M.mem x N ∧ M.PairMember I x d₀.val T)
    (dc₁ : ∀ x, M.mem x D₁ ↔ M.mem x N ∧ M.PairMember I x d₁.val T)
    (dc₂ : ∀ x, M.mem x D₂ ↔ M.mem x N ∧ M.PairMember I x d₂.val T)
    (ft₀₁ : Fn0_d D₁ D₀ t₀₁) (ft₁₂ : Fn0_d D₂ D₁ t₁₂) (ft₀₂ : Fn0_d D₂ D₀ t₀₂)
    (g₀₁ : ∀ x y : (smdl_structure_l I (R := T) nx).Domain, Rd_entry_d x.val y.val t₀₁ ↔ Rd_entry_d x y r₀₁)
    (g₁₂ : ∀ x y : (smdl_structure_l I (R := T) nx).Domain, Rd_entry_d x.val y.val t₁₂ ↔ Rd_entry_d x y r₁₂)
    (g₀₂ : ∀ x y : (smdl_structure_l I (R := T) nx).Domain, Rd_entry_d x.val y.val t₀₂ ↔ Rd_entry_d x y r₀₂)
    (rp₀ : Rp_map_d I D₀ X V₀ G₀ p₀ C₀) (rp₁ : Rp_map_d I D₁ X V₁ G₁ p₁ C₁) (rp₂ : Rp_map_d I D₂ X V₂ G₂ p₂ C₂)
    (fK₀₁ : M.IsSetFunctionFromTo I K₀₁ G₀ G₁) (fK₁₂ : M.IsSetFunctionFromTo I K₁₂ G₁ G₂)
    (k₀₁ : ∀ f g, M.PairMember I f g K₀₁ → Cp0_d D₁ D₀ X t₀₁ f g)
    (k₁₂ : ∀ f g, M.PairMember I f g K₁₂ → Cp0_d D₂ D₁ X t₁₂ f g)
    (k₀₂ : ∀ f g, M.mem f G₀ → M.mem g G₂ → Cp0_d D₂ D₀ X t₀₂ f g → M.PairMember I f g K₀₂)
    (fj₀₁ : M.IsSetFunctionFromTo I j₀₁ C₀ C₁) (fj₁₂ : M.IsSetFunctionFromTo I j₁₂ C₁ C₂)
    (fj₀₂ : M.IsSetFunctionFromTo I j₀₂ C₀ C₂)
    (lift₀₁ : Rp_lift_d I K₀₁ p₀ p₁ j₀₁) (lift₁₂ : Rp_lift_d I K₁₂ p₁ p₂ j₁₂) (lift₀₂ : Rp_lift_d I K₀₂ p₀ p₂ j₀₂) :
    Cp0_d D₂ D₁ D₀ t₁₂ t₀₁ t₀₂ ∧
      ∀ B C, M.PairMember I B C j₀₂ ↔ M.mem B C₀ ∧ ∃ A, M.PairMember I B A j₀₁ ∧ M.PairMember I A C j₁₂ := by
  obtain ⟨s, comp⟩ := cp0_exists_l hN fq₀₁ fq₁₂
  have factor := Cp0_d.assoc_l fq₁₂ fq₀₁ comp fa f₁₂ f₀₁
  have eq := ec_factor_unique_l hN.1 inj comp.1 fq₀₂ factor f₀₂
  subst s
  have native := cp0_projection_comp_l fq₀₁ fq₁₂ comp space fr₀₁ fr₁₂ fr₀₂ r₀₁s r₁₂s r₀₂s
  have actual := smdl_graph_composition_l I nx d₀ d₁ d₂ r₀₁ r₁₂ r₀₂ dc₀ dc₁ dc₂ ft₀₂ g₀₁ g₁₂ g₀₂ native
  exact ⟨actual, rs_projection_comp_l I rp₀ rp₁ rp₂ ft₀₁ ft₁₂ actual fK₀₁ fK₁₂ k₀₁ k₁₂ k₀₂
    fj₀₁ fj₁₂ fj₀₂ lift₀₁ lift₁₂ lift₀₂⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 对象码分量间的实际统一过渡

箭头只记录同一坐标重排下的代表复合。任意代表均实现同一箭头；
规范坐标的唯一性把任意公式见证识别到实际构造的完整初等映射。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal FilterZF
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

def Er_arrow_d (ω L N T ξ ℓ z Y a b B C : M.Domain) : Prop := ∃ D E t f g,
  Er_coord_d I ω L N T ξ ℓ z a b D E t ∧ Fn0_d D Y f ∧ M.mem f B ∧ M.mem g C ∧ Cp0_d E D Y t f g

def er_arrow_m {n} (ω L N T ξ ℓ z Y a b B C : Term n) : Formula 1 n := set[n] ⟪∃ D E t f g,
  ⌜er_coord_m⌝ₚ(⌜ω⌝ₛ, ⌜L⌝ₛ, ⌜N⌝ₛ, ⌜T⌝ₛ, ⌜ξ⌝ₛ, ⌜ℓ⌝ₛ, ⌜z⌝ₛ, ⌜a⌝ₛ, ⌜b⌝ₛ, D, E, t) ∧
  ⌜fn0_m⌝ₚ(D, ⌜Y⌝ₛ, f) ∧ f ∈ ⌜B⌝ₛ ∧ g ∈ ⌜C⌝ₛ ∧ ⌜cp0_m⌝ₚ(E, D, ⌜Y⌝ₛ, t, f, g)⟫
derive_free_closed er_arrow_m

theorem er_arrow_sat_l (ext : Extensional M) {n} (ρ : Env M n) (ω L N T ξ ℓ z Y a b B C : Term n) :
    Formula.satisfies ρ (er_arrow_m ω L N T ξ ℓ z Y a b B C) ↔
      Er_arrow_d I (ω.eval ρ) (L.eval ρ) (N.eval ρ) (T.eval ρ) (ξ.eval ρ) (ℓ.eval ρ)
        (z.eval ρ) (Y.eval ρ) (a.eval ρ) (b.eval ρ) (B.eval ρ) (C.eval ρ) := by
  simp only [er_arrow_m, Er_arrow_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    er_coord_sat_l I ext, fn0_sat_l ext, Formula.satisfies_mem_iff, cp0_sat_l ext, Definitional.Term.eval_weaken]; rfl

variable (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "Kp" => kp_pair_l (ZF.modelsKP hZF)

/-- 规范模型表的两个条目自动生成实际初等过渡，公式准确读取其整个图。 -/
theorem It_local_d.code_map_l {ω c X R c' Y S q Γ H k N T z L a b o₀ o₁ r : M.Domain}
    (hω : M.IsOmega ω) (ex : Rf_ext_d Kp X R) (mx : Smdl_d Kp c X R)
    (theory : Sc_theory_d Kp ω X R) (collection : Sc_collection_d Kp ω X R)
    (model : Smdl_d Kp c' Y S) (hq : Smap_d Kp ω c c' X Y q)
    (nx : ∃ x, M.mem x N) (hN : (smdl_structure_l Kp (R := T) nx).Models KP)
    (U w ξ ℓ f : (smdl_structure_l Kp (R := T) nx).Domain)
    (numbers : Rr_layer_d Kp ω N T w.val z) (finite : Fs_read_d w U)
    (powers : ∀ m d : (smdl_structure_l Kp (R := T) nx).Domain,
      (smdl_structure_l Kp (R := T) nx).mem m w → Ep_space_d ξ m d →
        ∃ p, (smdl_structure_l Kp (R := T) nx).IsPowerSetOf p d)
    (products : ∀ m n d e : (smdl_structure_l Kp (R := T) nx).Domain,
      (smdl_structure_l Kp (R := T) nx).mem m w → (smdl_structure_l Kp (R := T) nx).mem n w → Ep_space_d ξ m d → Ep_space_d ξ n e →
        ∃ B, (smdl_structure_l Kp (R := T) nx).mem B U ∧ (smdl_structure_l Kp (R := T) nx).IsCartesianProduct (kp_pair_l hN) B d e)
    (carrier : ∀ x, M.mem x Γ ↔ M.mem x N ∧ Rd_entry_d x U.val T)
    (ownerClosed : Rr_closed_d Kp N T U.val) (fk : M.IsSetInjectionFromTo Kp k Γ Y)
    (image : ∀ y, Rd_entry_d y H S ↔ ∃ x, M.mem x Γ ∧ Rd_entry_d x y k)
    (pred : ∀ x y, Rd_entry_d x y k → ∀ v, Rd_entry_d v y S ↔ ∃ s, Rd_entry_d s x T ∧ Rd_entry_d s v k)
    (closed : Rr_closed_d Kp Y S H) (small : Rr_small_d Kp Y S H)
    (hξ : (smdl_structure_l Kp (R := T) nx).mem ξ U)
    (length : ∀ x, M.mem x L ↔ M.mem x N ∧ Rd_entry_d x ℓ.val T)
    (edge : Ei_map_d ω L a b r) (inj : ∀ i j x, Rd_entry_d i x b → Rd_entry_d j x b → i = j)
    (first : Er_code_d Kp ω L N T ξ.val f.val z Y S k a o₀)
    (last : Er_code_d Kp ω L N T ξ.val f.val z Y S k b o₁)
    (loc : It_local_d Kp w.val N T ξ.val ℓ.val f.val) :
    ∃ j C₀ W₀ C₁ W₁, Smdl_d Kp o₀ C₀ W₀ ∧ Smdl_d Kp o₁ C₁ W₁ ∧ Smap_d Kp ω o₀ o₁ C₀ C₁ j ∧
      (∀ B C, Rd_entry_d B C j ↔ M.mem B C₀ ∧ M.mem C C₁ ∧
        Er_arrow_d Kp ω L N T ξ.val ℓ.val z Y a b B C) ∧
      ∃ D E t, Er_coord_d Kp ω L N T ξ.val ℓ.val z a b D E t ∧
        ∀ B C, Rd_entry_d B C j → ∀ g, M.mem g B → ∃ h, M.mem h C ∧ Cp0_d E D Y t g h := by
  obtain ⟨m, m', a', d, u, hm, fa, hmm, fna, ga, fa', ds, hd, hau,
    D, i₀, t₀, d₀, P, V₀, G₀, p₀, C₀, W₀, dc, fi₀, id₀, rt₀, ft₀, hdd,
    ownerP, sourceP, ultra₀, su, family₀, quotient₀⟩ :=
    first.read_l hZF hω mx theory model hq nx hN U w ξ ℓ f numbers finite powers
      carrier ownerClosed fk image pred closed hξ length loc
  obtain ⟨n, n', b', e, v, hn, fb, hnn, fnb, gb, fb', es, he, hbv,
    E, i₁, t₁, e₀, Q, V₁, G₁, p₁, C₁, W₁, ec, fi₁, id₁, rt₁, ft₁, hee,
    ownerQ, sourceQ, ultra₁, sv, family₁, quotient₁⟩ :=
    last.read_l hZF hω mx theory model hq nx hN U w ξ ℓ f numbers finite powers
      carrier ownerClosed fk image pred closed hξ length loc
  obtain ⟨m₀, n₀, _, _, fr, fb₀, factor⟩ := edge
  have eq := factor.1.domain_eq_l hZF.1 fa
  subst m₀
  have eq := fb₀.domain_eq_l hZF.1 fb
  subst n₀
  obtain ⟨r', p, fr', factor', _, fp, ps, t, K, j, ft, graph, _, fK, graphK, embed, lift, _⟩ :=
    loc.raw_projection_l hZFC hω ex mx theory collection model hq nx hN U w ξ ℓ f
      m' n' b' a' d e u v numbers finite.transitive
      (products n' m' e d ((numbers.image n'.val).mpr ⟨n, hn, hnn⟩)
        ((numbers.image m'.val).mpr ⟨m, hm, hmm⟩) es ds)
      carrier ownerClosed fk image pred small hd he length
      hm hn fr factor hmm hnn fb' fa' gb ga ds es hbv hau dc ec fi₀ fi₁ id₀ id₁ rt₀ rt₁ ft₀ ft₁ hdd hee
      ownerP ownerQ sourceP sourceQ ultra₀ ultra₁ su sv family₀ family₁ quotient₀ quotient₁
  have coord := Er_coord_d.of_native_l Kp nx hN.1 ξ ℓ a' b' d e p
    ⟨m, m'.val, hm, fa, hmm, fna, ga⟩ ⟨n, n'.val, hn, fb, hnn, fnb, gb⟩
    ⟨m', n', r', fa', fb', fr', factor', ds, es, fp, ps⟩ dc ec ft graph
  have any B C (hBC : Rd_entry_d B C j) g (hg : M.mem g B) : ∃ h, M.mem h C ∧ Cp0_d E D Y t g h := by
    have gp := quotient₀.map.member_l Kp hZF.1 ultra₀.base (embed.1.1.input_mem_of_pairMember hBC) hg
    obtain ⟨h, hh, hgh⟩ := fK.2.2 g (quotient₀.map.projection.input_mem_of_pairMember gp)
    obtain ⟨C', _, hp⟩ := quotient₁.map.projection.2.2 h hh
    have eq := embed.1.1.1.2 B C' C (lift g h B C' hgh gp hp) hBC
    exact ⟨h, eq ▸ quotient₁.map.representative_l Kp ultra₁.base hp, ((graphK g h).mp hgh).2.2⟩
  refine ⟨j, C₀, W₀, C₁, W₁, quotient₀.code, quotient₁.code, embed, ?_, D, E, t, coord, any⟩
  intro B C
  constructor
  · intro hBC
    have hB := embed.1.1.input_mem_of_pairMember hBC
    obtain ⟨g, gp⟩ := (quotient₀.map.range B).mp hB
    have hg := quotient₀.map.representative_l Kp ultra₀.base gp
    obtain ⟨h, hh, comp⟩ := any B C hBC g hg
    exact ⟨hB, embed.1.1.output_mem_of_pairMember hBC, D, E, t, g, h, coord,
      quotient₀.map.functions g (quotient₀.map.projection.input_mem_of_pairMember gp), hg, hh, comp⟩
  · rintro ⟨hB, hC, D', E', t', g, h, coord', _, hg, hh, comp⟩
    obtain ⟨eqD, eqE, eqt⟩ := coord'.unique_l hZF numbers hN.1 ξ ℓ
      (fun x hx => ((length x).mp hx).1) inj coord
    subst D'
    subst E'
    subst t'
    have gp := quotient₀.map.member_l Kp hZF.1 ultra₀.base hB hg
    have hp := quotient₁.map.member_l Kp hZF.1 ultra₁.base hC hh
    exact lift g h B C ((graphK g h).mpr
      ⟨quotient₀.map.projection.input_mem_of_pairMember gp, quotient₁.map.projection.input_mem_of_pairMember hp, comp⟩) gp hp


section Reflexivity
variable (hZ : M.Models ZF)
local notation "J" => kp_pair_l (ZF.modelsKP hZ)

/-- 同一分量的每个商类都有实际恒等箭头，代表取自原来的商类。 -/
theorem Er_code_d.arrow_refl_l {ω c X R c' Y S q Γ H k N T z L a o C W B : M.Domain}
    (hω : M.IsOmega ω) (mx : Smdl_d J c X R)
    (theory : Sc_theory_d J ω X R) (model : Smdl_d J c' Y S) (hq : Smap_d J ω c c' X Y q)
    (nx : ∃ x, M.mem x N) (hN : (smdl_structure_l J (R := T) nx).Models KP)
    (U w ξ ℓ f : (smdl_structure_l J (R := T) nx).Domain)
    (numbers : Rr_layer_d J ω N T w.val z) (finite : Fs_read_d w U)
    (powers : ∀ m d : (smdl_structure_l J (R := T) nx).Domain,
      (smdl_structure_l J (R := T) nx).mem m w → Ep_space_d ξ m d →
        ∃ p, (smdl_structure_l J (R := T) nx).IsPowerSetOf p d)
    (carrier : ∀ x, M.mem x Γ ↔ M.mem x N ∧ Rd_entry_d x U.val T)
    (ownerClosed : Rr_closed_d J N T U.val) (fk : M.IsSetInjectionFromTo J k Γ Y)
    (image : ∀ y, Rd_entry_d y H S ↔ ∃ x, M.mem x Γ ∧ Rd_entry_d x y k)
    (pred : ∀ x y, Rd_entry_d x y k → ∀ v, Rd_entry_d v y S ↔ ∃ s, Rd_entry_d s x T ∧ Rd_entry_d s v k)
    (closed : Rr_closed_d J Y S H) (hξ : (smdl_structure_l J (R := T) nx).mem ξ U)
    (length : ∀ x, M.mem x L ↔ M.mem x N ∧ Rd_entry_d x ℓ.val T)
    (loc : It_local_d J w.val N T ξ.val ℓ.val f.val)
    (code : Er_code_d J ω L N T ξ.val f.val z Y S k a o)
    (pair : KPair_d M o C W) (hB : M.mem B C) : Er_arrow_d J ω L N T ξ.val ℓ.val z Y a a B B := by
  obtain ⟨n, m, b, d, u, hn, fa, hnm, fn, ga, fb, ds, _, _,
    D, _, _, _, _, V, G, p, C', W', dc, _, _, _, _, _, _, _, ultra, _, _, quotient⟩ :=
    code.read_l hZ hω mx theory model hq nx hN U w ξ ℓ f numbers finite powers
      carrier ownerClosed fk image pred closed hξ length loc
  obtain ⟨rfl, rfl⟩ := kpair_injective_l M pair quotient.code.1
  obtain ⟨g, gp⟩ := (quotient.map.range B).mp hB
  have hg := quotient.map.representative_l J ultra.base gp
  have fg := quotient.map.functions g (quotient.map.projection.input_mem_of_pairMember gp)
  obtain ⟨t, coord, id⟩ := Er_coord_d.refl_l hZ nx hN ξ ℓ m b d
    ⟨n, m.val, hn, fa, hnm, fn, ga⟩ fb ds dc
  refine ⟨D, D, t, g, g, coord, fg, hg, hg, fg, fun s hs => ?_⟩
  obtain ⟨x, hx, hsx⟩ := fg.2.1 s hs
  exact ⟨s, hs, x, hx, (id s s).mpr ⟨hs, rfl⟩, hsx, hsx⟩

end Reflexivity

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原关系全部分量的统一过渡图与标签集合

模型表、全部标签节点、标签函数、过渡关系和分量关系均实际生成。
每一对可比支撑的完整初等映射由规范码直接读取，不另设系统律前提。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

structure Er_graph_d (ω L N T ξ ℓ F z Y S k J O Z A p V W : M.Domain) : Prop where
  order : Di_order_d J O
  order_spec : ∀ a b, Rd_entry_d a b O ↔ M.mem a J ∧ M.mem b J ∧ ∃ r, Ei_map_d ω L a b r
  indices : ∀ a, M.mem a J ↔ Ei_d ω L a
  codes : ∃ Q, Fn0_d J Q Z
  components : ∀ a o, Rd_entry_d a o Z → Er_code_d I ω L N T ξ F z Y S k a o
  projection : Fn0_d A J p
  nodes : ∀ u, M.mem u A ↔ ∃ a B, KPair_d M u a B ∧ Ep_at_d Z a B
  index : ∀ u a B, KPair_d M u a B → (Rd_entry_d u a p ↔ M.mem u A)
  arrows : ∀ u v, Rd_entry_d u v V ↔ M.mem u A ∧ M.mem v A ∧
    ∃ a b B C, KPair_d M u a B ∧ KPair_d M v b C ∧ Rd_entry_d a b O ∧ Er_arrow_d I ω L N T ξ ℓ z Y a b B C
  relations : ∀ u v, Rd_entry_d u v W ↔ M.mem u A ∧ M.mem v A ∧
    ∃ a B C, KPair_d M u a B ∧ KPair_d M v a C ∧ Ep_rel_d Z a B C
  transition : ∀ a b, Rd_entry_d a b O → ∃ j o₀ C₀ W₀ o₁ C₁ W₁,
    Rd_entry_d a o₀ Z ∧ Rd_entry_d b o₁ Z ∧ Smdl_d I o₀ C₀ W₀ ∧ Smdl_d I o₁ C₁ W₁ ∧
    Smap_d I ω o₀ o₁ C₀ C₁ j ∧
    (∀ B C, Rd_entry_d B C j ↔ M.mem B C₀ ∧ M.mem C C₁ ∧ Er_arrow_d I ω L N T ξ ℓ z Y a b B C) ∧
    ∃ D E t, Er_coord_d I ω L N T ξ ℓ z a b D E t ∧
      ∀ B C, Rd_entry_d B C j → ∀ g, M.mem g B → ∃ h, M.mem h C ∧ Cp0_d E D Y t g h

section Reading
variable {I : kpair_convention_l.Interpretation M} {ω L N T ξ ℓ F z Y S k J O Z A p V W : M.Domain}

theorem Er_graph_d.at_l (h : Er_graph_d I ω L N T ξ ℓ F z Y S k J O Z A p V W)
    {u a B} (hu : M.mem u A) (pair : KPair_d M u a B) : Ep_at_d Z a B := by
  obtain ⟨b, C, pair', hb⟩ := (h.nodes u).mp hu
  obtain ⟨rfl, rfl⟩ := kpair_injective_l M pair pair'
  exact hb

theorem Er_graph_d.label_l (h : Er_graph_d I ω L N T ξ ℓ F z Y S k J O Z A p V W)
    {u a} (hua : Rd_entry_d u a p) : ∃ B, KPair_d M u a B ∧ Ep_at_d Z a B := by
  obtain ⟨b, B, hu, hat⟩ := (h.nodes u).mp (h.projection.bound_l hua).1
  have hub := (h.index u b B hu).mpr (h.projection.bound_l hua).1
  have eq := h.projection.2.2 u (h.projection.bound_l hua).1 b (h.projection.bound_l hub).2
    a (h.projection.bound_l hua).2 hub hua
  exact ⟨B, eq ▸ hu, eq ▸ hat⟩

theorem Er_graph_d.arrow_l (h : Er_graph_d I ω L N T ξ ℓ F z Y S k J O Z A p V W)
    {u v a b B C} (hu : KPair_d M u a B) (hv : KPair_d M v b C) :
    Rd_entry_d u v V ↔ M.mem u A ∧ M.mem v A ∧ Rd_entry_d a b O ∧ Er_arrow_d I ω L N T ξ ℓ z Y a b B C := by
  refine (h.arrows u v).trans ⟨?_, fun ⟨huA, hvA, hab⟩ => ⟨huA, hvA, a, b, B, C, hu, hv, hab⟩⟩
  rintro ⟨huA, hvA, a', b', B', C', hu', hv', hab⟩
  obtain ⟨rfl, rfl⟩ := kpair_injective_l M hu hu'
  obtain ⟨rfl, rfl⟩ := kpair_injective_l M hv hv'
  exact ⟨huA, hvA, hab⟩

theorem Er_graph_d.relation_l (h : Er_graph_d I ω L N T ξ ℓ F z Y S k J O Z A p V W)
    {u v a B C} (hu : KPair_d M u a B) (hv : KPair_d M v a C) :
    Rd_entry_d u v W ↔ M.mem u A ∧ M.mem v A ∧ Ep_rel_d Z a B C := by
  refine (h.relations u v).trans ⟨?_, fun ⟨huA, hvA, hab⟩ => ⟨huA, hvA, a, B, C, hu, hv, hab⟩⟩
  rintro ⟨huA, hvA, a', B', C', hu', hv', hab⟩
  obtain ⟨rfl, rfl⟩ := kpair_injective_l M hu hu'
  obtain ⟨_, rfl⟩ := kpair_injective_l M hv hv'
  exact ⟨huA, hvA, hab⟩

end Reading

section Representatives
variable {I : kpair_convention_l.Interpretation M} {ω L N T ξ ℓ F z Y S k J O Z A p V W : M.Domain}

/-- 实际系统边可以从源类中的任意代表读取。 -/
theorem Er_graph_d.lift_l (ext : Extensional M) (h : Er_graph_d I ω L N T ξ ℓ F z Y S k J O Z A p V W)
    {u v a b B C g : M.Domain} (hu : KPair_d M u a B) (hv : KPair_d M v b C)
    (edge : Rd_entry_d u v V) (hg : M.mem g B) :
    ∃ D E t f, Er_coord_d I ω L N T ξ ℓ z a b D E t ∧ M.mem f C ∧ Cp0_d E D Y t g f := by
  obtain ⟨huA, hvA, hab, arrow⟩ := (h.arrow_l hu hv).mp edge
  obtain ⟨j, o₀, C₀, W₀, o₁, C₁, W₁, hao, hbo, m₀, m₁, _, spec, D, E, t, coord, any⟩ := h.transition a b hab
  obtain ⟨_, table⟩ := h.codes
  have pair o C W (hc : I.Codes o C W) : KPair_d M o C W := by
    let ρ : Env M 3 := ⟨Fin.cases o (Fin.cases C (fun _ => W)), fun _ => o⟩
    exact (kpair_sat_l M ext ρ .newest (.bound 1) (.bound 2)).mp
      ((I.satisfies_code_iff ρ .newest (.bound 1) (.bound 2)).mpr hc)
  have hj := (spec B C).mpr ⟨(ep_at_read_l table hao (pair o₀ C₀ W₀ m₀.1)).mp (h.at_l huA hu),
    (ep_at_read_l table hbo (pair o₁ C₁ W₁ m₁.1)).mp (h.at_l hvA hv), arrow⟩
  obtain ⟨f, hf, comp⟩ := any B C hj g hg
  exact ⟨D, E, t, f, coord, hf, comp⟩

end Representatives

variable (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "Kp" => kp_pair_l (ZF.modelsKP hZF)

/-- 原模型表和两个有限幂的实际乘积，直接生成全部支撑间的初等过渡图。 -/
theorem It_local_d.code_graphs_l {ω c X R c' Y S q Γ H k N T z : M.Domain}
    (hω : M.IsOmega ω) (ex : Rf_ext_d Kp X R) (mx : Smdl_d Kp c X R)
    (theory : Sc_theory_d Kp ω X R) (collection : Sc_collection_d Kp ω X R)
    (model : Smdl_d Kp c' Y S) (hq : Smap_d Kp ω c c' X Y q)
    (nx : ∃ x, M.mem x N) (hN : (smdl_structure_l Kp (R := T) nx).Models KP)
    (U w ξ ℓ f : (smdl_structure_l Kp (R := T) nx).Domain)
    (numbers : Rr_layer_d Kp ω N T w.val z) (finite : Fs_read_d w U)
    (powers : ∀ m d : (smdl_structure_l Kp (R := T) nx).Domain,
      (smdl_structure_l Kp (R := T) nx).mem m w → Ep_space_d ξ m d →
        ∃ p, (smdl_structure_l Kp (R := T) nx).IsPowerSetOf p d)
    (products : ∀ m n d e : (smdl_structure_l Kp (R := T) nx).Domain,
      (smdl_structure_l Kp (R := T) nx).mem m w → (smdl_structure_l Kp (R := T) nx).mem n w → Ep_space_d ξ m d → Ep_space_d ξ n e →
        ∃ B, (smdl_structure_l Kp (R := T) nx).mem B U ∧ (smdl_structure_l Kp (R := T) nx).IsCartesianProduct (kp_pair_l hN) B d e)
    (carrier : ∀ x, M.mem x Γ ↔ M.mem x N ∧ Rd_entry_d x U.val T)
    (ownerClosed : Rr_closed_d Kp N T U.val) (fk : M.IsSetInjectionFromTo Kp k Γ Y)
    (image : ∀ y, Rd_entry_d y H S ↔ ∃ x, M.mem x Γ ∧ Rd_entry_d x y k)
    (pred : ∀ x y, Rd_entry_d x y k → ∀ v, Rd_entry_d v y S ↔ ∃ s, Rd_entry_d s x T ∧ Rd_entry_d s v k)
    (closed : Rr_closed_d Kp Y S H) (small : Rr_small_d Kp Y S H)
    (hξ : (smdl_structure_l Kp (R := T) nx).mem ξ U)
    (loc : It_local_d Kp w.val N T ξ.val ℓ.val f.val) :
    ∃ L J O Z A p V W, (∀ x, M.mem x L ↔ M.mem x N ∧ Rd_entry_d x ℓ.val T) ∧
      Er_graph_d Kp ω L N T ξ.val ℓ.val f.val z Y S k J O Z A p V W := by
  obtain ⟨L, J, O, Z, Q, length, indices, order, os, table, codes⟩ :=
    loc.code_table_l hZF hω ex mx theory collection model hq nx hN U w ξ ℓ f numbers finite
      powers carrier ownerClosed fk image pred closed small hξ
  -- 结构码的三次并集给出所有商类的统一集合界。
  obtain ⟨Q₁, h₁⟩ := KP.exists_union (ZF.modelsKP hZF) Q
  obtain ⟨Q₂, h₂⟩ := KP.exists_union (ZF.modelsKP hZF) Q₁
  obtain ⟨P, hP⟩ := KP.exists_union (ZF.modelsKP hZF) Q₂
  have bound a B (hat : Ep_at_d Z a B) : M.mem a J ∧ M.mem B P := by
    obtain ⟨o, C, W, hao, ⟨s, t, hs, _, pair⟩, hB⟩ := hat
    have hCQ := (h₂ C).mpr ⟨s, (h₁ s).mpr ⟨o, (table.bound_l hao).2, (pair s).mpr (Or.inl rfl)⟩, (hs C).mpr rfl⟩
    exact ⟨(table.bound_l hao).1, (hP B).mpr ⟨C, hCQ, hB⟩⟩
  obtain ⟨B, bs⟩ := ZF.exists_cartesianProduct hZF Kp J P
  let φ : UnarySchema 1 := { body := .existsE (.existsE (.conj (kpair_m (.bound 2) (.bound 1) .newest)
    (ep_at_m (.bound 3) (.bound 1) .newest))) }
  let η : Env M 1 := ⟨fun _ => Z, fun _ => Z⟩
  obtain ⟨A, as⟩ := ZF.separation_exists_d hZF φ η B
  have node u : M.mem u A ↔ ∃ a B, KPair_d M u a B ∧ Ep_at_d Z a B := by
    have sat : φ.denote η u ↔ ∃ a B, KPair_d M u a B ∧ Ep_at_d Z a B := by
      simp only [φ, UnarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
        kpair_sat_l M hZF.1, ep_at_sat_l hZF.1]; rfl
    refine (as u).trans ((and_congr_right fun _ => sat).trans ⟨And.right, fun ⟨a, C, hu, hat⟩ => ?_⟩)
    exact ⟨(bs u).mpr ⟨a, (bound a C hat).1, C, (bound a C hat).2, hu⟩, a, C, hu, hat⟩
  let ψ : BinarySchema 0 := { body := .existsE (kpair_m (.bound 2) (.bound 1) .newest) }
  let ρ : Env M 0 := ⟨Fin.elim0, fun _ => Z⟩
  have sat u a : ψ.denote ρ u a ↔ ∃ B, KPair_d M u a B := by
    simp only [ψ, BinarySchema.denote, Formula.satisfies_exists_iff, kpair_sat_l M hZF.1]; rfl
  obtain ⟨p, fp, ps⟩ := ZF.exists_setFunctionFromTo_of_denote hZF Kp ψ ρ (source := A) (target := J)
    (fun u hu => by
      obtain ⟨a, B, hu, _⟩ := (node u).mp hu
      exact ⟨a, (sat u a).mpr ⟨B, hu⟩⟩)
    (fun u _ a b ha hb => by
      obtain ⟨B, hu⟩ := (sat u a).mp ha
      obtain ⟨C, hv⟩ := (sat u b).mp hb
      exact (kpair_injective_l M hu hv).1)
    (fun u a hu ha => by
      obtain ⟨b, B, hb, hat⟩ := (node u).mp hu
      obtain ⟨C, hc⟩ := (sat u a).mp ha
      exact (kpair_injective_l M hb hc).1 ▸ (bound b B hat).1)
  have index u a B (hu : KPair_d M u a B) : Rd_entry_d u a p ↔ M.mem u A :=
    ⟨fp.input_mem_of_pairMember, fun huA => (ps u a).mpr ⟨huA, (sat u a).mpr ⟨B, hu⟩⟩⟩
  let env : Env M 9 := ⟨Fin.cases O (Fin.cases Y (Fin.cases z (Fin.cases ℓ.val (Fin.cases ξ.val
    (Fin.cases T (Fin.cases N (Fin.cases L (fun _ => ω)))))))), fun _ => ω⟩
  let arrow : BinarySchema 9 := {
    body := .existsE (.existsE (.existsE (.existsE (.conj (kpair_m (.bound 5) (.bound 3) (.bound 1))
      (.conj (kpair_m (.bound 4) (.bound 2) .newest) (.conj (rd_entry0_m (.bound 3) (.bound 2) (.bound 6))
        (er_arrow_m (.bound 14) (.bound 13) (.bound 12) (.bound 11) (.bound 10) (.bound 9)
          (.bound 8) (.bound 7) (.bound 3) (.bound 2) (.bound 1) .newest))))))) }
  obtain ⟨V, _, vs⟩ := ZF.exists_setRelationOn_of_denote hZF Kp arrow env A
  have arrows u v : Rd_entry_d u v V ↔ M.mem u A ∧ M.mem v A ∧
      ∃ a b B C, KPair_d M u a B ∧ KPair_d M v b C ∧ Rd_entry_d a b O ∧ Er_arrow_d Kp ω L N T ξ.val ℓ.val z Y a b B C := by
    simpa only [arrow, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      kpair_sat_l M hZF.1, rd_entry0_sat_l hZF.1, er_arrow_sat_l Kp hZF.1] using! vs u v
  let relation : BinarySchema 1 := { body := .existsE (.existsE (.existsE (.conj
    (kpair_m (.bound 4) (.bound 2) (.bound 1)) (.conj (kpair_m (.bound 3) (.bound 2) .newest)
      (ep_rel_m (.bound 5) (.bound 2) (.bound 1) .newest))))) }
  obtain ⟨W, _, ws⟩ := ZF.exists_setRelationOn_of_denote hZF Kp relation η A
  have relations u v : Rd_entry_d u v W ↔ M.mem u A ∧ M.mem v A ∧
      ∃ a B C, KPair_d M u a B ∧ KPair_d M v a C ∧ Ep_rel_d Z a B C := by
    simpa only [relation, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      kpair_sat_l M hZF.1, ep_rel_sat_l hZF.1] using! ws u v
  refine ⟨L, J, O, Z, A, p, V, W, length, order, os, indices, ⟨Q, table⟩,
    fun a o hao => ((codes a o).mp hao).2, fn0_of_function_l (ZF.modelsKP hZF) fp, node, index, arrows, relations, ?_⟩
  intro a b hab
  obtain ⟨ha, hb, r, edge⟩ := (os a b).mp hab
  obtain ⟨o₀, _, hao⟩ := table.2.1 a ha
  obtain ⟨o₁, _, hbo⟩ := table.2.1 b hb
  obtain ⟨_, _, _, inj⟩ := (indices b).mp hb
  obtain ⟨j, C₀, W₀, C₁, W₁, first, last, embed, spec, any⟩ :=
    loc.code_map_l hZFC hω ex mx theory collection model hq nx hN U w ξ ℓ f numbers finite powers products
      carrier ownerClosed fk image pred closed small hξ length edge inj ((codes a o₀).mp hao).2 ((codes b o₁).mp hbo).2
  exact ⟨j, o₀, C₀, W₀, o₁, C₁, W₁, hao, hbo, first, last, embed, spec, any⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 全部对象码分量的实际定向系统

恒等箭头来自原商类中的代表，复合箭头来自原坐标函数的实际复合。
唯一性、单射性及关系保持均读取已经构造的完整初等映射。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "Kp" => kp_pair_l (ZF.modelsKP hZF)

theorem It_local_d.code_system_l {ω c X R c' Y S q Γ H k N T z : M.Domain}
    (hω : M.IsOmega ω) (ex : Rf_ext_d Kp X R) (mx : Smdl_d Kp c X R)
    (theory : Sc_theory_d Kp ω X R) (collection : Sc_collection_d Kp ω X R)
    (model : Smdl_d Kp c' Y S) (hq : Smap_d Kp ω c c' X Y q)
    (nx : ∃ x, M.mem x N) (hN : (smdl_structure_l Kp (R := T) nx).Models KP)
    (U w ξ ℓ f : (smdl_structure_l Kp (R := T) nx).Domain)
    (numbers : Rr_layer_d Kp ω N T w.val z) (finite : Fs_read_d w U)
    (powers : ∀ m d : (smdl_structure_l Kp (R := T) nx).Domain,
      (smdl_structure_l Kp (R := T) nx).mem m w → Ep_space_d ξ m d →
        ∃ p, (smdl_structure_l Kp (R := T) nx).IsPowerSetOf p d)
    (products : ∀ m n d e : (smdl_structure_l Kp (R := T) nx).Domain,
      (smdl_structure_l Kp (R := T) nx).mem m w → (smdl_structure_l Kp (R := T) nx).mem n w → Ep_space_d ξ m d → Ep_space_d ξ n e →
        ∃ B, (smdl_structure_l Kp (R := T) nx).mem B U ∧ (smdl_structure_l Kp (R := T) nx).IsCartesianProduct (kp_pair_l hN) B d e)
    (carrier : ∀ x, M.mem x Γ ↔ M.mem x N ∧ Rd_entry_d x U.val T)
    (ownerClosed : Rr_closed_d Kp N T U.val) (fk : M.IsSetInjectionFromTo Kp k Γ Y)
    (image : ∀ y, Rd_entry_d y H S ↔ ∃ x, M.mem x Γ ∧ Rd_entry_d x y k)
    (pred : ∀ x y, Rd_entry_d x y k → ∀ v, Rd_entry_d v y S ↔ ∃ s, Rd_entry_d s x T ∧ Rd_entry_d s v k)
    (closed : Rr_closed_d Kp Y S H) (small : Rr_small_d Kp Y S H)
    (hξ : (smdl_structure_l Kp (R := T) nx).mem ξ U)
    (loc : It_local_d Kp w.val N T ξ.val ℓ.val f.val) :
    ∃ L J O Z A p V W, (∀ x, M.mem x L ↔ M.mem x N ∧ Rd_entry_d x ℓ.val T) ∧
      Er_graph_d Kp ω L N T ξ.val ℓ.val f.val z Y S k J O Z A p V W ∧ Di_system_d J O A p V W := by
  obtain ⟨L, J, O, Z, A, p, V, W, length, h⟩ :=
    loc.code_graphs_l hZFC hω ex mx theory collection model hq nx hN U w ξ ℓ f
      numbers finite powers products carrier ownerClosed fk image pred closed small hξ
  obtain ⟨Q, table⟩ := h.codes
  have node a B (hat : Ep_at_d Z a B) : ∃ u, M.mem u A ∧ KPair_d M u a B ∧ Rd_entry_d u a p := by
    obtain ⟨u, hu⟩ := (Kp).total a B
    have huA := (h.nodes u).mpr ⟨a, B, hu, hat⟩
    exact ⟨u, huA, hu, (h.index u a B hu).mpr huA⟩
  have bounds u v (huv : Rd_entry_d u v V) : M.mem u A ∧ M.mem v A :=
    ⟨((h.arrows u v).mp huv).1, ((h.arrows u v).mp huv).2.1⟩
  have forward u v a b (hua : Rd_entry_d u a p) (hvb : Rd_entry_d v b p) (huv : Rd_entry_d u v V) : Rd_entry_d a b O := by
    obtain ⟨B, hu, _⟩ := h.label_l hua
    obtain ⟨C, hv, _⟩ := h.label_l hvb
    exact ((h.arrow_l hu hv).mp huv).2.2.1
  have maps a b (hab : Rd_entry_d a b O) : ∃ j o₀ C₀ W₀ o₁ C₁ W₁,
      Rd_entry_d a o₀ Z ∧ Rd_entry_d b o₁ Z ∧ Smdl_d Kp o₀ C₀ W₀ ∧ Smdl_d Kp o₁ C₁ W₁ ∧
      M.IsSetInjectionFromTo Kp j C₀ C₁ ∧
      (∀ B E B' E', Rd_entry_d B B' j → Rd_entry_d E E' j → (Rd_entry_d B E W₀ ↔ Rd_entry_d B' E' W₁)) ∧
      (∀ B C, Rd_entry_d B C j ↔ M.mem B C₀ ∧ M.mem C C₁ ∧ Er_arrow_d Kp ω L N T ξ.val ℓ.val z Y a b B C) ∧
      ∃ D E t, Er_coord_d Kp ω L N T ξ.val ℓ.val z a b D E t ∧
        ∀ B C, Rd_entry_d B C j → ∀ g, M.mem g B → ∃ h, M.mem h C ∧ Cp0_d E D Y t g h := by
    obtain ⟨j, o₀, C₀, W₀, o₁, C₁, W₁, hao, hbo, m₀, m₁, elem, spec, any⟩ := h.transition a b hab
    exact ⟨j, o₀, C₀, W₀, o₁, C₁, W₁, hao, hbo, m₀, m₁, elem.1,
      fun B E B' E' hb he => elem.relation_l Kp hZF hω m₀ m₁ hb he, spec, any⟩
  refine ⟨L, J, O, Z, A, p, V, W, length, h, h.order, h.projection, bounds, forward, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u huA
    obtain ⟨a, B, hu, o, C, W', hao, pair, hB⟩ := (h.nodes u).mp huA
    exact (h.arrow_l hu hu).mpr ⟨huA, huA, h.order.refl a (table.bound_l hao).1,
      (h.components a o hao).arrow_refl_l hZF hω mx theory model hq nx hN U w ξ ℓ f numbers finite powers
        carrier ownerClosed fk image pred closed hξ length loc pair hB⟩
  · intro u v x huv hvx
    -- 第二条箭头作用于第一条的同一个中间代表，再复合原坐标图。
    obtain ⟨a, B, hu, _⟩ := (h.nodes u).mp (bounds u v huv).1
    obtain ⟨b, C, hv, hvC⟩ := (h.nodes v).mp (bounds u v huv).2
    obtain ⟨c, D, hx, hxD⟩ := (h.nodes x).mp (bounds v x hvx).2
    have hab := ((h.arrow_l hu hv).mp huv).2.2.1
    have hbc := ((h.arrow_l hv hx).mp hvx).2.2.1
    obtain ⟨j, o₀, C₀, W₀, o₁, C₁, W₁, hbo, hco, m₀, m₁, _, _, spec, E', F, s, coord₁, any⟩ := maps b c hbc
    have hCD := (spec C D).mpr ⟨(ep_at_read_l table hbo m₀.1).mp hvC,
      (ep_at_read_l table hco m₁.1).mp hxD, ((h.arrow_l hv hx).mp hvx).2.2.2⟩
    obtain ⟨D₀, E, t, g, v', coord₀, fg, hg, hv', pull⟩ := ((h.arrow_l hu hv).mp huv).2.2.2
    obtain ⟨x', hx', pull'⟩ := any C D hCD v' hv'
    obtain ⟨eq, r, coord₂, comp⟩ := coord₀.comp_l hZF numbers hN ξ ℓ coord₁
    subst E'
    obtain ⟨_, _, _, _, _, _, _, _, _, _, ft, _⟩ := coord₀
    obtain ⟨_, _, _, _, _, _, _, _, _, _, fs, _⟩ := coord₁
    exact (h.arrow_l hu hx).mpr ⟨(bounds u v huv).1, (bounds v x hvx).2, h.order.trans a b c hab hbc,
      D₀, F, r, g, x', coord₂, fg, hg, hx', Cp0_d.assoc_l ft fs comp fg pull pull'⟩
  · intro u a b hua hab
    obtain ⟨B, hu, hat⟩ := h.label_l hua
    obtain ⟨j, o₀, C₀, W₀, o₁, C₁, W₁, hao, hbo, m₀, m₁, fj, _, spec, _⟩ := maps a b hab
    obtain ⟨C, hC, hBC⟩ := fj.1.2.2 B ((ep_at_read_l table hao m₀.1).mp hat)
    obtain ⟨v, hvA, hv, hvb⟩ := node b C ⟨o₁, C₁, W₁, hbo, m₁.1, hC⟩
    exact ⟨v, hvb, (h.arrow_l hu hv).mpr ⟨(h.projection.bound_l hua).1, hvA, hab, ((spec B C).mp hBC).2.2⟩⟩
  · intro u v x b hvb hxb huv hux
    obtain ⟨a, _, hua⟩ := h.projection.2.1 u (bounds u v huv).1
    obtain ⟨B, hu, huB⟩ := h.label_l hua
    obtain ⟨C, hv, hvC⟩ := h.label_l hvb
    obtain ⟨D, hx, hxD⟩ := h.label_l hxb
    obtain ⟨j, o₀, C₀, W₀, o₁, C₁, W₁, hao, hbo, m₀, m₁, fj, _, spec, _⟩ := maps a b (forward u v a b hua hvb huv)
    have hB := (ep_at_read_l table hao m₀.1).mp huB
    have hC := (ep_at_read_l table hbo m₁.1).mp hvC
    have hD := (ep_at_read_l table hbo m₁.1).mp hxD
    have eq := fj.1.1.2 B C D ((spec B C).mpr ⟨hB, hC, ((h.arrow_l hu hv).mp huv).2.2.2⟩)
      ((spec B D).mpr ⟨hB, hD, ((h.arrow_l hu hx).mp hux).2.2.2⟩)
    exact kpair_unique_l M hZF.1 (eq ▸ hv) hx
  · intro u v x a hua hva hux hvx
    obtain ⟨b, _, hxb⟩ := h.projection.2.1 x (bounds u x hux).2
    obtain ⟨B, hu, huB⟩ := h.label_l hua
    obtain ⟨C, hv, hvC⟩ := h.label_l hva
    obtain ⟨D, hx, hxD⟩ := h.label_l hxb
    obtain ⟨j, o₀, C₀, W₀, o₁, C₁, W₁, hao, hbo, m₀, m₁, fj, _, spec, _⟩ := maps a b (forward u x a b hua hxb hux)
    have hB := (ep_at_read_l table hao m₀.1).mp huB
    have hC := (ep_at_read_l table hao m₀.1).mp hvC
    have hD := (ep_at_read_l table hbo m₁.1).mp hxD
    have eq := fj.2 B C D ((spec B D).mpr ⟨hB, hD, ((h.arrow_l hu hx).mp hux).2.2.2⟩)
      ((spec C D).mpr ⟨hC, hD, ((h.arrow_l hv hx).mp hvx).2.2.2⟩)
    exact kpair_unique_l M hZF.1 (eq ▸ hu) hv
  · intro u v huv
    obtain ⟨huA, hvA, a, B, C, hu, hv, _⟩ := (h.relations u v).mp huv
    exact ⟨a, (h.index u a B hu).mpr huA, (h.index v a C hv).mpr hvA⟩
  · intro u v a x y b hua hva hxb hyb hux hvy
    obtain ⟨B, hu, huB⟩ := h.label_l hua
    obtain ⟨C, hv, hvC⟩ := h.label_l hva
    obtain ⟨D, hx, hxD⟩ := h.label_l hxb
    obtain ⟨E, hy, hyE⟩ := h.label_l hyb
    obtain ⟨j, o₀, C₀, W₀, o₁, C₁, W₁, hao, hbo, m₀, m₁, _, rel, spec, _⟩ := maps a b (forward u x a b hua hxb hux)
    have hB := (ep_at_read_l table hao m₀.1).mp huB
    have hC := (ep_at_read_l table hao m₀.1).mp hvC
    have hD := (ep_at_read_l table hbo m₁.1).mp hxD
    have hE := (ep_at_read_l table hbo m₁.1).mp hyE
    have old : Rd_entry_d u v W ↔ Rd_entry_d B C W₀ := (h.relation_l hu hv).trans
      ⟨fun hh => (ep_rel_read_l table hao m₀.1).mp hh.2.2, fun hh =>
        ⟨(h.projection.bound_l hua).1, (h.projection.bound_l hva).1, (ep_rel_read_l table hao m₀.1).mpr hh⟩⟩
    have new : Rd_entry_d x y W ↔ Rd_entry_d D E W₁ := (h.relation_l hx hy).trans
      ⟨fun hh => (ep_rel_read_l table hbo m₁.1).mp hh.2.2, fun hh =>
        ⟨(h.projection.bound_l hxb).1, (h.projection.bound_l hyb).1, (ep_rel_read_l table hbo m₁.1).mpr hh⟩⟩
    exact old.trans ((rel B C D E ((spec B D).mpr ⟨hB, hD, ((h.arrow_l hu hx).mp hux).2.2.2⟩)
      ((spec C E).mpr ⟨hC, hE, ((h.arrow_l hv hy).mp hvy).2.2.2⟩)).trans new.symm)

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原对象码系统的完整内部初等性

真实分量与标签分量共用同一个去标签同构。逐支撑初等映射经这两个
同构接入原关系定向极限定理，覆盖背景模型的全部内部公式码。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
variable {ω L N T ξ ℓ F z Y S k J O Z A p V W : M.Domain}

theorem Er_graph_d.elementary_l (hω : M.IsOmega ω)
    (h : Er_graph_d I ω L N T ξ ℓ F z Y S k J O Z A p V W) :
    Di_elementary_d I ω O A p V W := by
  obtain ⟨_, table⟩ := h.codes
  intro a b c X R d Q U stage₀ stage₁ hab
  obtain ⟨j, o₀, C₀, W₀, o₁, C₁, W₁, hao, hbo, m₀, m₁, elem, spec, _⟩ := h.transition a b hab
  obtain ⟨e, _, he, _, es, _⟩ := ep_tag_l hZF hω h.codes h.nodes h.index h.label_l h.relation_l stage₀ hao m₀
  obtain ⟨_, u, _, hu, _, us⟩ := ep_tag_l hZF hω h.codes h.nodes h.index h.label_l h.relation_l stage₁ hbo m₁
  obtain ⟨v, hv, vs⟩ := smap_comp_l I hZF he elem
  obtain ⟨w, hw, ws⟩ := smap_comp_l I hZF hv hu
  refine ⟨w, hw, fun x y => ⟨?_, ?_⟩⟩
  · intro hxy
    obtain ⟨hxX, D, hxD, hDy⟩ := (ws x y).mp hxy
    obtain ⟨_, B, hxB, hBD⟩ := (vs x D).mp hxD
    obtain ⟨_, hpx⟩ := (es x B).mp hxB
    obtain ⟨hyQ, hpy⟩ := (us D y).mp hDy
    exact ⟨hxX, hyQ, (h.arrow_l hpx hpy).mpr ⟨((stage₀.2.1 x).mp hxX).1,
      ((stage₁.2.1 y).mp hyQ).1, hab, ((spec B D).mp hBD).2.2⟩⟩
  · rintro ⟨hxX, hyQ, hxy⟩
    obtain ⟨B, hpx, hat⟩ := h.label_l (((stage₀.2.1 x).mp hxX).2)
    obtain ⟨D, hpy, hbt⟩ := h.label_l (((stage₁.2.1 y).mp hyQ).2)
    have hBD := (spec B D).mpr ⟨(ep_at_read_l table hao m₀.1).mp hat,
      (ep_at_read_l table hbo m₁.1).mp hbt, ((h.arrow_l hpx hpy).mp hxy).2.2.2⟩
    exact (ws x y).mpr ⟨hxX, D, (vs x D).mpr ⟨hxX, B, (es x B).mpr ⟨hxX, hpx⟩, hBD⟩,
      (us D y).mpr ⟨hyQ, hpy⟩⟩

/-- 每个原商分量到同一原关系极限的完整初等嵌入及精确代表方程。 -/
theorem Er_graph_d.stage_l (hω : M.IsOmega ω)
    (h : Er_graph_d I ω L N T ξ ℓ F z Y S k J O Z A p V W)
    (diagram : Di_system_d J O A p V W) {r o C U a d D R : M.Domain}
    (limit : Di_limit_d A p V W r C U) (model : Smdl_d I o C U)
    (had : Rd_entry_d a d Z) (stage : Smdl_d I d D R) :
    ∃ j, Smap_d I ω d o D C j ∧
      ∀ B E, Rd_entry_d B E j ↔ M.mem B D ∧ ∃ u, KPair_d M u a B ∧ Rd_entry_d u E r := by
  obtain ⟨B, hB⟩ := stage.2.1
  obtain ⟨u, hu⟩ := (I).total a B
  have huA := (h.nodes u).mpr ⟨a, B, hu, d, D, R, had, stage.1, hB⟩
  obtain ⟨d', D', R', localStage⟩ := di_stage_exists_l hZF diagram ((h.index u a B hu).mpr huA)
  obtain ⟨_, e, _, he, _, es⟩ := ep_tag_l hZF hω h.codes h.nodes h.index h.label_l h.relation_l localStage had stage
  obtain ⟨v, hv, vs⟩ := di_elementary_limit_l hZF hω diagram limit (h.elementary_l hZF hω) localStage model
  obtain ⟨j, hj, js⟩ := smap_comp_l I hZF he hv
  refine ⟨j, hj, fun B E => (js B E).trans (and_congr_right fun hB => ?_)⟩
  apply exists_congr
  intro u
  refine ⟨fun ⟨hBu, huE⟩ => ⟨((es B u).mp hBu).2, ((vs u E).mp huE).2⟩, fun ⟨hu, huE⟩ => ?_⟩
  have huA := (h.nodes u).mpr ⟨a, B, hu, d, D, R, had, stage.1, hB⟩
  have huD := (localStage.2.1 u).mpr ⟨huA, (h.index u a B hu).mpr huA⟩
  exact ⟨(es B u).mpr ⟨huD, hu⟩, (vs u E).mpr ⟨huD, huE⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原关系全部支撑系统的统一编码

分量仍读取所属模型中的原测度和前驱模型中的实际函数码。过渡、任意代表
提升及全部内部有限支撑同时进入同一公式；后继树记录保存这个实际系统。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

def er_graph_m {d} (ω L N T ξ ℓ F z Y S k J O Z A p V W : Term d) : Formula 1 d := set[d] ⟪
  ⌜di_order_m⌝ₚ(⌜J⌝ₛ, ⌜O⌝ₛ) ∧
  (∀ a b, ⌜rd_entry0_m⌝ₚ(a, b, ⌜O⌝ₛ) ↔ a ∈ ⌜J⌝ₛ ∧ b ∈ ⌜J⌝ₛ ∧
    (∃ r, ⌜ei_map_m⌝ₚ(⌜ω⌝ₛ, ⌜L⌝ₛ, a, b, r))) ∧
  (∀ a, a ∈ ⌜J⌝ₛ ↔ ⌜ei_m⌝ₚ(⌜ω⌝ₛ, ⌜L⌝ₛ, a)) ∧
  (∃ Q, ⌜fn0_m⌝ₚ(⌜J⌝ₛ, Q, ⌜Z⌝ₛ)) ∧
  (∀ a o, ⌜rd_entry0_m⌝ₚ(a, o, ⌜Z⌝ₛ) →
    ⌜er_code_m⌝ₚ(⌜ω⌝ₛ, ⌜L⌝ₛ, ⌜N⌝ₛ, ⌜T⌝ₛ, ⌜ξ⌝ₛ, ⌜F⌝ₛ, ⌜z⌝ₛ, ⌜Y⌝ₛ, ⌜S⌝ₛ, ⌜k⌝ₛ, a, o)) ∧
  ⌜fn0_m⌝ₚ(⌜A⌝ₛ, ⌜J⌝ₛ, ⌜p⌝ₛ) ∧
  (∀ u, u ∈ ⌜A⌝ₛ ↔ ∃ a B, ⌜kpair0_m⌝ₚ(u, a, B) ∧ ⌜ep_at_m⌝ₚ(⌜Z⌝ₛ, a, B)) ∧
  (∀ u a B, ⌜kpair0_m⌝ₚ(u, a, B) → (⌜rd_entry0_m⌝ₚ(u, a, ⌜p⌝ₛ) ↔ u ∈ ⌜A⌝ₛ)) ∧
  (∀ u v, ⌜rd_entry0_m⌝ₚ(u, v, ⌜V⌝ₛ) ↔ u ∈ ⌜A⌝ₛ ∧ v ∈ ⌜A⌝ₛ ∧
    (∃ a b B C, ⌜kpair0_m⌝ₚ(u, a, B) ∧ ⌜kpair0_m⌝ₚ(v, b, C) ∧ ⌜rd_entry0_m⌝ₚ(a, b, ⌜O⌝ₛ) ∧
      ⌜er_arrow_m⌝ₚ(⌜ω⌝ₛ, ⌜L⌝ₛ, ⌜N⌝ₛ, ⌜T⌝ₛ, ⌜ξ⌝ₛ, ⌜ℓ⌝ₛ, ⌜z⌝ₛ, ⌜Y⌝ₛ, a, b, B, C))) ∧
  (∀ u v, ⌜rd_entry0_m⌝ₚ(u, v, ⌜W⌝ₛ) ↔ u ∈ ⌜A⌝ₛ ∧ v ∈ ⌜A⌝ₛ ∧
    (∃ a B C, ⌜kpair0_m⌝ₚ(u, a, B) ∧ ⌜kpair0_m⌝ₚ(v, a, C) ∧ ⌜ep_rel_m⌝ₚ(⌜Z⌝ₛ, a, B, C))) ∧
  (∀ a b, ⌜rd_entry0_m⌝ₚ(a, b, ⌜O⌝ₛ) → ∃ j o₀ C₀ W₀ o₁ C₁ W₁,
    ⌜rd_entry0_m⌝ₚ(a, o₀, ⌜Z⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(b, o₁, ⌜Z⌝ₛ) ∧
    ⌜smdl_m (𝒞 := kpair_convention_l)⌝ₚ(o₀, C₀, W₀) ∧ ⌜smdl_m (𝒞 := kpair_convention_l)⌝ₚ(o₁, C₁, W₁) ∧
    ⌜smap_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ, o₀, o₁, C₀, C₁, j) ∧
    (∀ B C, ⌜rd_entry0_m⌝ₚ(B, C, j) ↔ B ∈ C₀ ∧ C ∈ C₁ ∧
      ⌜er_arrow_m⌝ₚ(⌜ω⌝ₛ, ⌜L⌝ₛ, ⌜N⌝ₛ, ⌜T⌝ₛ, ⌜ξ⌝ₛ, ⌜ℓ⌝ₛ, ⌜z⌝ₛ, ⌜Y⌝ₛ, a, b, B, C)) ∧
    (∃ D E t, ⌜er_coord_m⌝ₚ(⌜ω⌝ₛ, ⌜L⌝ₛ, ⌜N⌝ₛ, ⌜T⌝ₛ, ⌜ξ⌝ₛ, ⌜ℓ⌝ₛ, ⌜z⌝ₛ, a, b, D, E, t) ∧
      (∀ B C, ⌜rd_entry0_m⌝ₚ(B, C, j) → ∀ g ∈ B, ∃ h ∈ C, ⌜cp0_m⌝ₚ(E, D, ⌜Y⌝ₛ, t, g, h))))⟫
derive_free_closed er_graph_m

theorem er_graph_sat_l (ext : Extensional M) {d} (ρ : Env M d)
    (ω L N T ξ ℓ F z Y S k J O Z A p V W : Term d) :
    Formula.satisfies ρ (er_graph_m ω L N T ξ ℓ F z Y S k J O Z A p V W) ↔
      Er_graph_d I (ω.eval ρ) (L.eval ρ) (N.eval ρ) (T.eval ρ) (ξ.eval ρ) (ℓ.eval ρ)
        (F.eval ρ) (z.eval ρ) (Y.eval ρ) (S.eval ρ) (k.eval ρ) (J.eval ρ) (O.eval ρ)
        (Z.eval ρ) (A.eval ρ) (p.eval ρ) (V.eval ρ) (W.eval ρ) := by
  simp only [er_graph_m, Formula.satisfies_conj_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_iff_iff, Formula.satisfies_imp_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_forallMem_iff, Formula.satisfies_existsMem_iff, Formula.satisfies_mem_iff,
    di_order_sat_l ext, rd_entry0_sat_l ext, ei_map_sat_l ext, ei_sat_l ext, fn0_sat_l ext,
    kpair0_sat_l ext, er_code_sat_l I ext, ep_at_sat_l ext, er_arrow_sat_l I ext,
    ep_rel_sat_l ext, smdl_sat_l I, smap_sat_l I ext, er_coord_sat_l I ext,
    cp0_sat_l ext, Definitional.Term.eval_weaken]
  exact ⟨fun ⟨a, b, c, d, e, f, g, h, i, j, k⟩ => ⟨a, b, c, d, e, f, g, h, i, j, k⟩,
    fun h => ⟨h.order, h.order_spec, h.indices, h.codes, h.components, h.projection,
      h.nodes, h.index, h.arrows, h.relations, h.transition⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal
