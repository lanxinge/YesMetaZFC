import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawCopyClass
import YesMetaZFC.Model.SetTheory.ReducedPower.RelationPowerCount
import YesMetaZFC.SetTheory.InaccessibleEnumeration
import YesMetaZFC.SetTheory.CumulativeComparison
import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawGraphSyntax
import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawConstant
import YesMetaZFC.SetTheory.Card.CountableUnion
import YesMetaZFC.SetTheory.Card.FiniteSequenceCountable
import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawAlphabet
import YesMetaZFC.Model.SetTheory.Relations.CollectCode

/-! # 实际扩展器分量的幂集计数

直接读取原分量码的坐标、测度和函数族。有限幂在父模型共同秩段中的
成员性给出 δ 大小界；由原幂集可数构造该分量中整个幂集像的可数载体。
不假设所属模型或父模型整体可数。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal FilterZF
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Er_code_d.power_count_l {Ω c Y S Γ k N T z L a o B : M.Domain}
    (hΩ : M.IsOmega Ω) (model : Smdl_d I c Y S) (ext : Rf_ext_d I Y S)
    (theory : Sc_theory_d I Ω Y S)
    (ground : (smdl_structure_l I (R := S) model.2.1).Models ZFC)
    (nx : ∃ x, M.mem x N) (hN : (smdl_structure_l I (R := T) nx).Models KP)
    (U w ξ ℓ f : (smdl_structure_l I (R := T) nx).Domain)
    (ω δ α H P : (smdl_structure_l I (R := S) model.2.1).Domain)
    (hω : (smdl_structure_l I (R := S) model.2.1).IsOmega ω)
    (above : (smdl_structure_l I (R := S) model.2.1).mem ω δ)
    (regular : (smdl_structure_l I (R := S) model.2.1).IsRegularCardinal
      (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l ground))) δ)
    (strong : (smdl_structure_l I (R := S) model.2.1).IsStrongLimitCardinal
      (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l ground))) δ)
    (below : (smdl_structure_l I (R := S) model.2.1).MemberSubset α δ)
    (rank : V_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l ground))) α H)
    (power : (smdl_structure_l I (R := S) model.2.1).IsPowerSetOf P δ)
    (powerCarrier : ∀ x, M.mem x B ↔ M.mem x Y ∧ Rd_entry_d x P.val S)
    (count : M.CardinalLessOrEqual I B Ω)
    (numbers : Rr_layer_d I Ω N T w.val z) (finite : Fs_read_d w U)
    (powers : ∀ m d : (smdl_structure_l I (R := T) nx).Domain,
      (smdl_structure_l I (R := T) nx).mem m w → Ep_space_d ξ m d →
        ∃ p, (smdl_structure_l I (R := T) nx).IsPowerSetOf p d)
    (carrier : ∀ x, M.mem x Γ ↔ M.mem x N ∧ Rd_entry_d x U.val T)
    (ownerClosed : Rr_closed_d I N T U.val) (fk : M.IsSetInjectionFromTo I k Γ Y)
    (image : ∀ y, Rd_entry_d y H.val S ↔ ∃ x, M.mem x Γ ∧ Rd_entry_d x y k)
    (pred : ∀ x y, Rd_entry_d x y k → ∀ v, Rd_entry_d v y S ↔ ∃ s, Rd_entry_d s x T ∧ Rd_entry_d s v k)
    (closed : Rr_closed_d I Y S H.val) (hξ : (smdl_structure_l I (R := T) nx).mem ξ U)
    (length : ∀ x, M.mem x L ↔ M.mem x N ∧ Rd_entry_d x ℓ.val T)
    (loc : It_local_d I w.val N T ξ.val ℓ.val f.val)
    (code : Er_code_d I Ω L N T ξ.val f.val z Y S k a o) :
    ∃ D t d V G p C W A F K,
      Rp_model_d I D Y V S o G p C W ∧ Base_d D V ∧ Proper_d V ∧
      Fn0_d D Y t ∧ Rc_family_d I Y S D d t G ∧
      M.mem F G ∧ Rs_const_d D P.val F ∧ Rd_entry_d F A p ∧
      (∀ x, M.mem x K ↔ M.mem x C ∧ Rd_entry_d x A W) ∧ M.CardinalLessOrEqual I K Ω := by
  let Yn := smdl_structure_l I (R := S) model.2.1
  have native := ZFC.models_zf_l ground
  let J := kp_pair_l (ZF.modelsKP native)
  obtain ⟨q,identity,_⟩ := smap_identity_l I hZF (X := Y) (c := c) hΩ
  obtain ⟨_,_,_,d,_,_,_,_,_,_,_,_,hd,_,
    D,_,t,y,_,V,G,p,C,W,dc,_,_,rt,ft,dy,_,_,ultra,_,family,quotient⟩ :=
    code.read_l hZF hΩ model theory model identity nx hN U w ξ ℓ f numbers finite powers
      carrier ownerClosed fk image pred closed hξ length loc
  let d' : Yn.Domain := ⟨y,fk.1.output_mem_of_pairMember dy⟩
  have member : Yn.mem d' H := (image y).mpr ⟨d.val,(carrier d.val).mpr ⟨d.property,hd⟩,dy⟩
  have sub : Yn.MemberSubset d' H := v_transitive_l J rank d' member
  obtain ⟨i,hi⟩ := ZF.exists_inclusionInjection native J sub
  obtain ⟨Vδ,rankV⟩ := ZF.v_exists_l J native regular.isCardinal.1
  obtain ⟨e,he⟩ := ZFC.inaccessible_enumeration_l J ground hω above regular strong rankV
  obtain ⟨v,hv⟩ := ZF.exists_inverseBijection native J he
  obtain ⟨j,hj⟩ := ZF.exists_inclusionInjection native J (KP.v_compare_l (ZF.modelsKP native) rank rankV below).1
  obtain ⟨j,hj⟩ := ZF.exists_compositionInjection native J hj hv.1
  have small := ZF.exists_compositionInjection native J hi hj
  obtain ⟨v,hv⟩ := ZF.exists_inclusionInjection native J (regular.isCardinal.1.transitive ω above)
  have infinite : Yn.IsInfiniteCardinal J ω δ := ⟨regular.isCardinal,v,hv⟩
  have domain s x (sx : Rd_entry_d s x t) : Rd_entry_d x d'.val S :=
    (pred d.val y dy x).mpr ⟨s,((dc s).mp ((rt.2 s x).mp sx).1).2,((rt.2 s x).mp sx).2⟩
  -- 从同一实际分量产生 P 的常值代表，而非另选超幂或商模型。
  let ρ : Env Yn 0 := ⟨Fin.elim0,fun _ => d'⟩
  obtain ⟨Q,F,ff,constant⟩ := sc_constant_raw_l native.1 ρ (theory.algebra model.2.1 ρ) d' P
  obtain ⟨g,fg,read⟩ := smdl_function_l hZF model.2.1 native.1 d' Q F ff ft domain
  have codes := (rc_family_native_l I model.2.1 native.1 d' ft).mp family
  have hg := (codes g).mpr ⟨fg,Q,F,ff,read⟩
  have fixed : Rs_const_d D P.val g := by
    intro s hs
    obtain ⟨x,hx,sx⟩ := ft.2.1 s hs
    exact (read s ⟨x,hx⟩ P sx).mpr (constant ⟨x,hx⟩ (domain s x sx))
  obtain ⟨A,_,gA⟩ := quotient.map.projection.2.2 g hg
  obtain ⟨K,members,smallK⟩ := Rp_model_d.power_count_l hZF hΩ model ext theory native
    ω δ d' P hω infinite small power powerCarrier count ft domain ultra.base ultra.proper
      family quotient ⟨g,hg,fixed,gA⟩
  exact ⟨D,t,y,V,G,p,C,W,A,g,K,quotient,ultra.base,ultra.proper,ft,family,hg,fixed,gA,members,smallK⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 实际扩展器直接极限的幂集计数保持

每个支撑分量的幂集像已经可数。分量到原极限的实际初等图保持并反映
成员关系，且各处的常值 P 与同一原边的 P 像一致。可数支撑上的可定义
纤维覆盖因此枚举整个目标幂集，而非仅枚举旧子集的逐点像。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal FilterZF
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Er_graph_d.power_count_l
    {Ω c Y S Γ k N T z L J O Z A p V W r c' C R j P' B : M.Domain}
    (hΩ : M.IsOmega Ω) (model : Smdl_d I c Y S) (ext : Rf_ext_d I Y S)
    (theory : Sc_theory_d I Ω Y S)
    (ground : (smdl_structure_l I (R := S) model.2.1).Models ZFC)
    (nx : ∃ x, M.mem x N) (hN : (smdl_structure_l I (R := T) nx).Models KP)
    (U w ξ ℓ f : (smdl_structure_l I (R := T) nx).Domain)
    (ω δ α H P : (smdl_structure_l I (R := S) model.2.1).Domain)
    (hω : (smdl_structure_l I (R := S) model.2.1).IsOmega ω)
    (above : (smdl_structure_l I (R := S) model.2.1).mem ω δ)
    (regular : (smdl_structure_l I (R := S) model.2.1).IsRegularCardinal
      (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l ground))) δ)
    (strong : (smdl_structure_l I (R := S) model.2.1).IsStrongLimitCardinal
      (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l ground))) δ)
    (below : (smdl_structure_l I (R := S) model.2.1).MemberSubset α δ)
    (rank : V_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l ground))) α H)
    (power : (smdl_structure_l I (R := S) model.2.1).IsPowerSetOf P δ)
    (powerCarrier : ∀ x, M.mem x B ↔ M.mem x Y ∧ Rd_entry_d x P.val S)
    (count : M.CardinalLessOrEqual I B Ω) (supports : M.CardinalLessOrEqual I L Ω)
    (numbers : Rr_layer_d I Ω N T w.val z) (finite : Fs_read_d w U)
    (powers : ∀ m d : (smdl_structure_l I (R := T) nx).Domain,
      (smdl_structure_l I (R := T) nx).mem m w → Ep_space_d ξ m d →
        ∃ p, (smdl_structure_l I (R := T) nx).IsPowerSetOf p d)
    (carrier : ∀ x, M.mem x Γ ↔ M.mem x N ∧ Rd_entry_d x U.val T)
    (ownerClosed : Rr_closed_d I N T U.val) (fk : M.IsSetInjectionFromTo I k Γ Y)
    (image : ∀ y, Rd_entry_d y H.val S ↔ ∃ x, M.mem x Γ ∧ Rd_entry_d x y k)
    (pred : ∀ x y, Rd_entry_d x y k → ∀ v, Rd_entry_d v y S ↔ ∃ s, Rd_entry_d s x T ∧ Rd_entry_d s v k)
    (closed : Rr_closed_d I Y S H.val) (hξ : (smdl_structure_l I (R := T) nx).mem ξ U)
    (length : ∀ x, M.mem x L ↔ M.mem x N ∧ Rd_entry_d x ℓ.val T)
    (loc : It_local_d I w.val N T ξ.val ℓ.val f.val)
    (graph : Er_graph_d I Ω L N T ξ.val ℓ.val f.val z Y S k J O Z A p V W)
    (diagram : Di_system_d J O A p V W) (limit : Di_limit_d A p V W r C R)
    (target : Smdl_d I c' C R) (constants : Er_constants_d Y r j) (point : Rd_entry_d P.val P' j) :
    ∃ K, (∀ x, M.mem x K ↔ M.mem x C ∧ Rd_entry_d x P' R) ∧ M.CardinalLessOrEqual I K Ω := by
  obtain ⟨a₀,D₀,g₀,fg₀,fixed₀,repr₀⟩ := constants P.val P' point
  obtain ⟨F,seq,countF⟩ := ZF.fseq_countable_space_l I hZF hΩ supports
  obtain ⟨i,hi⟩ := ZF.exists_inclusionInjection hZF I (fun a ha => by
    obtain ⟨n,hn,fn,_⟩ := (graph.indices a).mp ha
    exact (seq a).mpr ⟨n,hn,fn0_function_l (ZF.modelsKP hZF) fn⟩)
  obtain ⟨s,hs⟩ := countF
  have countJ := ZF.exists_compositionInjection hZF I hi hs
  let χ : UnarySchema 2 := { body := rd_entry0_m .newest (.bound 1) (.bound 2) }
  obtain ⟨K,hK⟩ := ZF.separation_exists_d hZF χ ⟨Fin.cases P' (fun _ => R),fun _ => C⟩ C
  have members x : M.mem x K ↔ M.mem x C ∧ Rd_entry_d x P' R :=
    (hK x).trans (and_congr_right fun _ => rd_entry0_sat_l hZF.1 ..)
  let ρ : Env M 2 := ⟨Fin.cases p (fun _ => r),fun _ => C⟩
  let φ : BinarySchema 2 := {
    body := .existsE (.conj (rd_entry0_m .newest (.bound 2) (.bound 3))
      (rd_entry0_m .newest (.bound 1) (.bound 4))) }
  have sat a E : φ.denote ρ a E ↔ ∃ u, Rd_entry_d u a p ∧ Rd_entry_d u E r := by
    simp only [φ,BinarySchema.denote,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
      rd_entry0_sat_l hZF.1]
    rfl
  refine ⟨K,members,ZFC.countable_cover_l I hZFC hΩ φ ρ countJ ?_ ?_⟩
  · intro a ha Q fibre
    obtain ⟨_,table⟩ := graph.codes
    obtain ⟨o,_,ao⟩ := table.2.1 a ha
    obtain ⟨D,t,d,U',G,p',C',R',Pₐ,g,Kₐ,quotient,base,_,_,_,hg,fixed,gPₐ,memberₐ,countₐ⟩ :=
      (graph.components a o ao).power_count_l hZF hΩ model ext theory ground nx hN U w ξ ℓ f
        ω δ α H P hω above regular strong below rank power powerCarrier count numbers finite powers
          carrier ownerClosed fk image pred closed hξ length loc
    obtain ⟨q,map,leg⟩ := graph.stage_l hZF hΩ diagram limit target ao quotient.code
    have hPₐ := quotient.map.projection.output_mem_of_pairMember gPₐ
    obtain ⟨E,_,PE⟩ := map.1.1.2.2 Pₐ hPₐ
    obtain ⟨u,pair,ur⟩ := ((leg Pₐ E).mp PE).2
    have repr : Ep_repr_d r a g E :=
      ⟨u,Pₐ,pair,quotient.map.representative_l I base gPₐ,ur⟩
    have eq := graph.constant_l hZF nx (kp_pair_l hN) hN.1 w ξ ℓ f numbers length loc diagram limit
      (quotient.map.functions g hg) fg₀ fixed fixed₀ repr repr₀
    have PP : Rd_entry_d Pₐ P' q := eq ▸ PE
    obtain ⟨v,restriction⟩ := ZF.exists_restriction hZF I q Kₐ
    have fn := fn0_of_function_l (ZF.modelsKP hZF) (restriction.isSetFunctionFromTo map.1.1
      (fun x hx => ((memberₐ x).mp hx).1))
    have bound x y (xy : Rd_entry_d x y v) : M.mem y Q := by
      obtain ⟨hx,xy⟩ := (restriction.2 x y).mp xy
      obtain ⟨u,pair,uy⟩ := ((leg x y).mp xy).2
      have uyK := (members y).mpr ⟨map.1.1.output_mem_of_pairMember xy,
        (map.relation_l I hZF hΩ quotient.code target xy PP).mp ((memberₐ x).mp hx).2⟩
      exact (fibre y).mpr ⟨uyK,(sat a y).mpr
        ⟨u,(graph.index u a x pair).mpr (limit.projection.bound_l uy).1,uy⟩⟩
    have onto y (hy : M.mem y Q) : ∃ x, M.mem x Kₐ ∧ Rd_entry_d x y v := by
      obtain ⟨hyK,hy⟩ := (fibre y).mp hy
      obtain ⟨u,ua,uy⟩ := (sat a y).mp hy
      obtain ⟨x,pair,stored⟩ := graph.label_l ua
      have hx := (ep_at_read_l table ao quotient.code.1).mp stored
      have xy := (leg x y).mpr ⟨hx,u,pair,uy⟩
      have hxK := (memberₐ x).mpr ⟨hx,
        (map.relation_l I hZF hΩ quotient.code target xy PP).mpr ((members y).mp hyK).2⟩
      exact ⟨x,hxK,(restriction.2 x y).mpr ⟨hxK,xy⟩⟩
    exact ZF.ordinal_image_bound_l I hZF (hΩ.isOrdinal (ZF.modelsKP hZF)) countₐ
      (fn0_function_l (ZF.modelsKP hZF) (fn.retarget_l bound)) onto
  · intro E hE
    obtain ⟨u,uE⟩ := (limit.range E).mp ((members E).mp hE).1
    obtain ⟨a,ha,ua⟩ := graph.projection.2.1 u (limit.projection.bound_l uE).1
    exact ⟨a,ha,(sat a E).mpr ⟨u,ua,uE⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 同一次原生施加保持幂集计数不变量

所属侧的幂集计数控制实际支撑；父侧的幂集计数控制内部代表。
同一原边运输幂集公式，故输出计数属于给定 δ 像，无须重新选取后继。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Er_rank_cut_at_d.power_l
    {Ω c X R cA A S q Γ k N T z cN Ls Js Os Zs Ds ps Vs Ws rs cP P Rp j q' p₀ : M.Domain}
    (hΩ : M.IsOmega Ω) (root : Zc_model_d I Ω c X R)
    (ma : Smdl_d I cA A S) (fromA : Smap_d I Ω c cA X A q)
    (nx : ∃ x, M.mem x N) (native : (smdl_structure_l I (R := T) nx).Models ZF)
    (U w ξ ℓ e β X' K' jN δN : (smdl_structure_l I (R := T) nx).Domain)
    (data : Er_rank_cut_at_d hZF Ω c X R cA A S q Γ k N T z cN nx (ZF.modelsKP native)
      U w ξ ℓ e β X' K' jN Ls Js Os Zs Ds ps Vs Ws rs cP P Rp j q' p₀)
    (numbers : Rr_layer_d I Ω N T w.val z)
    (loc : It_local_d I w.val N T ξ.val ℓ.val e.val)
    (ordinal : (smdl_structure_l I (R := T) nx).IsOrdinal δN)
    (lengthBelow : (smdl_structure_l I (R := T) nx).mem ℓ δN)
    (ownerCount : Pc_count_d I Ω N T δN.val)
    (ω δ α H : (smdl_structure_l I (R := S) ma.2.1).Domain)
    (hω : (smdl_structure_l I (R := S) ma.2.1).IsOmega ω)
    (above : (smdl_structure_l I (R := S) ma.2.1).mem ω δ)
    (regular : (smdl_structure_l I (R := S) ma.2.1).IsRegularCardinal
      (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l ((root.map_l hZF hΩ ma fromA).native_l I hZF hΩ)))) δ)
    (strong : (smdl_structure_l I (R := S) ma.2.1).IsStrongLimitCardinal
      (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l ((root.map_l hZF hΩ ma fromA).native_l I hZF hΩ)))) δ)
    (rank : V_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l
      ((root.map_l hZF hΩ ma fromA).native_l I hZF hΩ)))) α H)
    (below : (smdl_structure_l I (R := S) ma.2.1).MemberSubset α δ)
    (image : ∀ y, Rd_entry_d y H.val S ↔ ∃ x, M.mem x Γ ∧ Rd_entry_d x y k)
    (parentCount : Pc_count_d I Ω A S δ.val) :
    ∀ δ', Rd_entry_d δ.val δ' j → Pc_count_d I Ω P Rp δ' := by
  have parent := root.map_l hZF hΩ ma fromA
  have ground := parent.native_l I hZF hΩ
  have hA := ZFC.models_zf_l ground
  obtain ⟨finite,closed,carrier,_,_,_,_,length,graph,diagram,limit,target,_,_,_,embed,_,
    constants,agree,_⟩ := data
  have supports := ownerCount.support_l hZF nx native δN ℓ ordinal lengthBelow length
  obtain ⟨B,C,power,members,count⟩ := parentCount.native_l hZF ma.2.1 δ
  have closedH : Rr_closed_d I A S H.val := fun a b ha hb haH sub =>
    v_subset_mem_l (kp_pair_l (ZF.modelsKP hA)) rank
      (A := ⟨a,ha⟩) (B := ⟨b,hb⟩) haH (fun x hx => sub x.val x.property hx)
  have powers m d (_ : (smdl_structure_l I (R := T) nx).mem m w) (_ : Ep_space_d ξ m d) :=
    ZF.exists_powerSet native d
  intro δ' point
  obtain ⟨B',hB',imageB⟩ := embed.1.1.2.2 B.val B.property
  obtain ⟨C',carrier',count'⟩ := graph.power_count_l hZFC hΩ ma parent.ext
    (parent.theory_l hZF hΩ) ground nx (ZF.modelsKP native) U w ξ ℓ e
      ω δ α H B hω above regular strong below rank power members count supports numbers finite powers
        carrier closed agree.injection image agree.predecessors closedH
          (by exact ((carrier ξ.val).mp agree.critical).2) length loc diagram limit target constants imageB
  let v : Fin 2 → (smdl_structure_l I (R := S) ma.2.1).Domain := Fin.cases B (fun _ => δ)
  have truth := (rr_truth_native_l I ma.2.1 (Formula.isPowerSet (.bound 0) (.bound 1))
      (by simp -implicitDefEqProofs) v).mpr
        ((Formula.satisfies_isPowerSet_iff ..).mpr power)
  have values : (fun i => (v i).val) =
      Fin.cases B.val (fun _ => δ.val) := funext (Fin.cases rfl (fun _ => rfl))
  rw [values] at truth
  exact ⟨B',C',truth.map_l I hZF hΩ ma target embed (by simp -implicitDefEqProofs)
    (Fin.cases imageB (fun _ => point)),carrier',count'⟩

end YesMetaZFC.SetTheory.LargeCardinal
