import YesMetaZFC.SetTheory.LargeCardinal.Absorption.BranchGeneric
import YesMetaZFC.Model.Forcing.Embedding.Rank
import YesMetaZFC.Model.SetTheory.Relations.RankImage
import YesMetaZFC.Model.Forcing.Collapse.ProductRealCollapse
import YesMetaZFC.Model.Forcing.Collapse.ProductTruthPrefix
import YesMetaZFC.Model.Forcing.Functions.ValueIsomorphism

/-! # 原吸收返回枝实际生产共同低秩层

原根切片逐点固定。小条件域属于原走法字母表，其秩下界使 κ 严格位于
该切片高度以下，因此原 Vκ 及其全部成员固定。原秩公式沿同一根腿运输，
得到目标中的同一个 Vκ，不把共同层或稠密集覆盖另外当作输入。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ag_branch_d.common_rank_l {Ω c X R z Q G b f : M.Domain} (hΩ : M.IsOmega Ω)
    (source : Smem_d I c X R) (trans : M.TransitiveSet X)
    (native : (smdl_structure_l I (R := R) source.1.2.1).Models ZF)
    {ω κ δ A V : (smdl_structure_l I (R := R) source.1.2.1).Domain}
    {p : Ag_forcing_d native ω κ δ A} (s : Ag_system_d native p)
    (hw : (smdl_structure_l I (R := R) source.1.2.1).IsOmega ω)
    (rank : V_d (kp_pair_l (ZF.modelsKP native)) κ V)
    (r : Ag_branch_d hZF Ω z c X Q G b (fun i => (s.aux_params_l native i).val) f) :
    Vr_d X κ.val V.val ∧ M.mem V.val r.N ∧ Vr_d r.N κ.val V.val ∧
      Rd_entry_d κ.val κ.val r.j ∧ Rd_entry_d V.val V.val r.j ∧
      ∀ x, M.mem x V.val → Rd_entry_d x x r.j := by
  let N := smdl_structure_l I (R := R) source.1.2.1
  let J := kp_pair_l (ZF.modelsKP native)
  obtain ⟨μ,K,hμ,hK,low,ha,point⟩ := r.low
  let μ₀ : N.Domain := ⟨μ,hμ⟩
  let K₀ : N.Domain := ⟨K,hK⟩
  have rank₀ : V_d J μ₀ K₀ := (rr_rank_native_l I source.1.2.1 (ZF.modelsKP native) μ₀ K₀).mp
    ((rr_rank_mem_l I (ZF.modelsKP hZF) source trans hμ hK).mpr low)
  have member {a d : N.Domain} : M.mem a.val d.val ↔ N.mem a d := (smem_member_l I source.1 source.2 a d).symm
  have ha₀ : N.mem s.A K₀ := member.mp ha
  have hQ : N.mem p.Q K₀ := (v_transitive_l J rank₀) s.A ha₀ p.Q ((s.source.alphabet p.Q).mpr (Or.inr s.source.full))
  have hκ := p.small_rank_l native hw rank₀ hQ
  have κμ := ZF.v_ordinal_height_l native rank₀ (v_ordinal_l J rank) hκ
  have hV := ZF.v_mem_l J native rank rank₀ κμ
  have fixedκ := point κ.val (member.mpr hκ)
  have fixedV := point V.val (member.mpr hV)
  have points x (hx : M.mem x V.val) := point x (low.transitive_l trans hK V.val (member.mpr hV) x hx)
  have old := (rr_rank_native_l I source.1.2.1 (ZF.modelsKP native) κ V).mpr rank
  have moved := ((rr_rank_truth_l I).mp old).map_l I hZF hΩ source.1 r.target.1 r.map
    (w := Fin.cases V.val (fun _ : Fin 1 => κ.val))
    (by simp -implicitDefEqProofs) (Fin.cases fixedV (fun _ => fixedκ))
  have hV' := r.map.1.1.output_mem_of_pairMember fixedV
  exact ⟨(rr_rank_mem_l I (ZF.modelsKP hZF) source trans κ.property V.property).mp old,hV',
    (rr_rank_mem_l I (ZF.modelsKP hZF) r.target r.transitive
      (r.map.1.1.output_mem_of_pairMember fixedκ) hV').mp ((rr_rank_truth_l I).mpr moved),fixedκ,fixedV,points⟩

/-- 给定共同层内的原偏序，实际保留旧泛型和所有低秩名字的完整值成员。 -/
theorem Ag_branch_d.low_lift_l {Ω c X R z Q G b f : M.Domain} (hΩ : M.IsOmega Ω)
    (source : Smem_d I c X R) (trans : M.TransitiveSet X)
    (native : (smdl_structure_l I (R := R) source.1.2.1).Models ZF)
    {ω κ δ A V P T : (smdl_structure_l I (R := R) source.1.2.1).Domain}
    {p : Ag_forcing_d native ω κ δ A} (s : Ag_system_d native p)
    (hw : (smdl_structure_l I (R := R) source.1.2.1).IsOmega ω)
    (rank : V_d (kp_pair_l (ZF.modelsKP native)) κ V)
    (r : Ag_branch_d hZF Ω z c X Q G b (fun i => (s.aux_params_l native i).val) f)
    (inside : (smdl_structure_l I (R := R) source.1.2.1).mem P V)
    (O : Cond_order_d (smdl_structure_l I (R := R) source.1.2.1) P T P)
    {H : (smdl_structure_l I (R := R) source.1.2.1).Domain → Prop} (generic : Generic_d _ P T P H) :
    let N := smdl_structure_l I (R := R) source.1.2.1
    let N' := smdl_structure_l I (R := r.W) r.target.1.2.1
    ∃ e : N.Domain → N'.Domain, Pe_d e ∧ (∀ a, Rd_entry_d a.val (e a).val r.j) ∧
      (∀ a, M.mem a.val V.val → (e a).val = a.val) ∧
      Generic_d N' (e P) (e T) (e P) (Em_generic_d e H) ∧
      (∀ q, Em_generic_d e H q ↔ ∃ p, H p ∧ p.val = q.val) ∧
      ∃ l : (extension_l N native P T P H).Domain → (extension_l N' r.native (e P) (e T) (e P) (Em_generic_d e H)).Domain,
        Function.Injective l ∧
        (∀ τ x, Qval_d N P T P H τ x → Qval_d N' (e P) (e T) (e P) (Em_generic_d e H) (e τ) (l x)) ∧
        Pe_d l ∧ ∀ τ : N.Domain, M.mem τ.val V.val → ∀ x, Qval_d N P T P H τ x → ∀ y,
          (extension_l N' r.native (e P) (e T) (e P) (Em_generic_d e H)).mem y (l x) ↔
            ∃ t, (extension_l N native P T P H).mem t x ∧ l t = y := by
  obtain ⟨rx,hV,ry,fixedκ,_,point⟩ := r.common_rank_l hZF hΩ source trans native s hw rank
  have hP := ((source.2 P.val V.val).mp inside).2.2
  obtain ⟨e,elem,values,generic',same,l,inj,names,elementary,full⟩ := r.map.rank_lift_l hZF hΩ trans r.transitive
    source r.target fixedκ (fun γ hγ => point γ (rx.ordinal_subset_l hZF trans V.property γ hγ))
    V.property rx hV ry native r.native P T P hP O generic
  exact ⟨e,elem,values,fun a ha => r.map.1.1.1.2 _ _ _ (values a) (point a.val ha),
    generic',same,l,inj,names,elementary,full⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 升高后的原全乘积泛型与原 R* 完整保持

共同 Vκ 覆盖原全乘积和规范实数并名字。原泛型提升命中目标全部稠密集；
低秩名字的值成员满性排除新的 R* 成员。两侧实数图经同一自然数坐标
逐边比较，故背景实数族字面相同，不仅是一一对应的副本。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ag_branch_d.old_product_l {Ω c X R z Q G b f H : M.Domain} (hΩ : M.IsOmega Ω)
    (source : Smem_d I c X R) (trans : M.TransitiveSet X)
    (native : (smdl_structure_l I (R := R) source.1.2.1).Models ZF)
    {ω κ δ A V A₀ P T W σ : (smdl_structure_l I (R := R) source.1.2.1).Domain}
    {p : Ag_forcing_d native ω κ δ A} (s : Ag_system_d native p)
    (hw : (smdl_structure_l I (R := R) source.1.2.1).IsOmega ω)
    (rank : V_d (kp_pair_l (ZF.modelsKP native)) κ V)
    (r : Ag_branch_d hZF Ω z c X Q G b (fun i => (s.aux_params_l native i).val) f)
    (inside : ∀ a, a ∈ [ω,P,σ] → (smdl_structure_l I (R := R) source.1.2.1).mem a V)
    (fa : (smdl_structure_l I (R := R) source.1.2.1).IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP native)) A₀ ω W)
    (product : Fp_product_d native ω A₀ P T) (name : Rp_name_d native ω A₀ P σ)
    (generic : Gset_d P.val T.val P.val X H) :
    let N := smdl_structure_l I (R := R) source.1.2.1
    let N' := smdl_structure_l I (R := r.W) r.target.1.2.1
    ∃ e : N.Domain → N'.Domain, Pe_d e ∧ (∀ a, Rd_entry_d a.val (e a).val r.j) ∧
      (∀ a, M.mem a.val V.val → (e a).val = a.val) ∧
      Fp_product_d r.native (e ω) (e A₀) (e P) (e T) ∧ Rp_name_d r.native (e ω) (e A₀) (e P) (e σ) ∧
      N'.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP r.native)) (e A₀) (e ω) (e W) ∧
      Gset_d (e P).val (e T).val (e P).val r.N H ∧
      ∀ x, Rp_bg_d hZF source native ω A₀ T H x ↔ Rp_bg_d hZF r.target r.native (e ω) (e A₀) (e T) H x := by
  let N := smdl_structure_l I (R := R) source.1.2.1
  let N' := smdl_structure_l I (R := r.W) r.target.1.2.1
  let U : N.Domain → Prop := fun a => M.mem a.val H
  have O := product.order_l native
  obtain ⟨sub,g⟩ := (source.generic_code_l I hZF.1 trans (ZF.modelsKP native) P T P H).mp generic
  obtain ⟨e,elem,values,fixed,g',same,l,li,names,elementary,full⟩ :=
    r.low_lift_l hZF hΩ source trans native s hw rank (inside P (by simp)) O g
  have low a (ha : a ∈ [ω,P,σ]) : M.mem a.val V.val := ((source.2 a.val V.val).mp (inside a ha)).2.2
  have eP : (e P).val = P.val := fixed P (low P (by simp))
  have predicate : Em_generic_d e U = (fun q : N'.Domain => M.mem q.val H) := by
    funext q
    apply propext
    exact (same q).trans ⟨fun ⟨a,ha,eq⟩ => eq ▸ ha,fun hq =>
      ⟨⟨q.val,trans P.val P.property q.val (sub q.val hq)⟩,hq,rfl⟩⟩
  have coded : Gset_d (e P).val (e T).val (e P).val r.N H :=
    (r.target.generic_code_l I hZF.1 r.transitive (ZF.modelsKP r.native) (e P) (e T) (e P) H).mpr
      ⟨fun q hq => eP.symm ▸ sub q hq,predicate ▸ g'⟩
  have product' := fp_product_image_l native r.native e elem product
  have name' := rp_name_image_l native r.native e elem name
  have hw' : N'.IsOmega (e ω) := by
    let ρ : Env N 1 := ⟨fun _ => ω,fun _ => ω⟩
    exact (Formula.satisfies_isOmega_iff (image_env_l e ρ) .newest).mp
      ((elem (Formula.isOmega .newest) (by simp -implicitDefEqProofs) ρ).mp
        ((Formula.satisfies_isOmega_iff ρ .newest).mpr hw))
  have fa' : N'.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP r.native)) (e A₀) (e ω) (e W) := by
    let ρ : Env N 3 := ⟨fun i => [A₀,ω,W].get i,fun _ => ω⟩
    let φ := Formula.isFunctionFromTo kpair_convention_l (.bound 0 : Term 3) (.bound 1) (.bound 2)
    exact (Formula.satisfies_isFunctionFromTo_iff (kp_pair_l (ZF.modelsKP r.native)) r.native.1 (image_env_l e ρ) _ _ _).mp
      ((elem φ (by simp -implicitDefEqProofs [φ]) ρ).mp
        ((Formula.satisfies_isFunctionFromTo_iff (kp_pair_l (ZF.modelsKP native)) native.1 ρ _ _ _).mpr fa))
  let E := extension_l N native P T P U
  let E' := extension_l N' r.native (e P) (e T) (e P) (Em_generic_d e U)
  have O' := product'.order_l r.native
  obtain ⟨j,ground,forward,backward⟩ := rp_background_l hZF source trans native hw fa product generic
  have target := rp_background_l hZF r.target r.transitive r.native hw' fa' product' coded
  dsimp only at target
  rw [← predicate] at target
  obtain ⟨k,base,forward',backward'⟩ := target
  obtain ⟨Z,vZ,members⟩ := name.value_l native hw fa product g
  obtain ⟨Z',vZ',members'⟩ := name'.value_l r.native hw' fa' product' g'
  have eqZ : Z' = l Z := qval_unique_l vZ' (names σ Z vZ)
  subst Z'
  have cover a (ha : N'.mem a (e ω)) : ∃ d, N.mem d ω ∧ e d = a := by
    have hω : M.mem a.val ω.val := fixed ω (low ω (by simp)) ▸ ((r.target.2 a.val (e ω).val).mp ha).2.2
    let d : N.Domain := ⟨a.val,trans ω.val ω.property a.val hω⟩
    have hd := (source.2 d.val ω.val).mpr ⟨d.property,ω.property,hω⟩
    have bound := (v_transitive_l (kp_pair_l (ZF.modelsKP native)) rank) ω (inside ω (by simp)) d hd
    exact ⟨d,hd,Subtype.ext (fixed d (((source.2 d.val V.val).mp bound).2.2))⟩
  have numbers a (ha : N.mem a ω) : (e a).val = a.val := fixed a
    (((source.2 a.val V.val).mp ((v_transitive_l (kp_pair_l (ZF.modelsKP native)) rank) ω (inside ω (by simp)) a ha)).2.2)
  -- 每个源实数沿同一个商提升保留背景图；只需自然数覆盖，不需整体满射。
  have read (y : E.Domain) (real : Rp_value_d native ω A₀ P T U y) {x : M.Domain}
      (decoded : Fn_read_d Subtype.val j y x) : Fn_read_d Subtype.val k (l y) x := by
    obtain ⟨τ,_,vy⟩ := value_name_l y
    have named : Fn_value_d native Subtype.val P T P ω τ U x :=
      ⟨j,y,vy,ground,real.function_l native hw fa product g j ground,decoded⟩
    obtain ⟨k₀,y',vy',base₀,_,decoded'⟩ := named.elementary_l native r.native e elem cover O g g'
      (fun p hp => ⟨p,hp,rfl⟩) numbers
    have eqk : k₀ = k := funext fun a => (base₀ a).unique_l O' r.native g' (base a)
    have eqy : y' = l y := qval_unique_l vy' (names τ y vy)
    simpa only [eqk,eqy] using decoded'
  refine ⟨e,elem,values,fixed,product',name',fa',coded,fun x => ⟨?_,?_⟩⟩
  · intro hx
    obtain ⟨y,⟨hy,decoded⟩,_⟩ := backward x hx
    have hy' : Rp_value_d r.native (e ω) (e A₀) (e P) (e T) (Em_generic_d e U) (l y) :=
      (members' (l y)).mp ((em_member_l l elementary y Z).mp ((members y).mpr hy))
    obtain ⟨_,x',⟨hx',decoded'⟩,_⟩ := forward' (l y) hy'
    have eq := (read y hy decoded).unique_l (ZF.modelsKP hZF) decoded'
      (fn0_function_l (ZF.modelsKP hZF) hx.1).1.1 (fn0_function_l (ZF.modelsKP hZF) hx'.1).1.1
    exact eq.symm ▸ hx'
  · intro hx
    obtain ⟨y,⟨hy,decoded⟩,_⟩ := backward' x hx
    obtain ⟨t,ht,eq⟩ := (full σ (low σ (by simp)) Z vZ y).mp ((members' y).mpr hy)
    have ht := (members t).mp ht
    obtain ⟨_,x',⟨hx',decoded'⟩,_⟩ := forward t ht
    have sameRead : Fn_read_d (N := N') (M := M) (E := E') Subtype.val k y x' := eq ▸ read t ht decoded'
    have eqx := decoded.unique_l (ZF.modelsKP hZF) sameRead
      (fn0_function_l (ZF.modelsKP hZF) hx.1).1.1 (fn0_function_l (ZF.modelsKP hZF) hx'.1).1.1
    exact eqx.symm ▸ hx'

end YesMetaZFC.SetTheory.LargeCardinal
