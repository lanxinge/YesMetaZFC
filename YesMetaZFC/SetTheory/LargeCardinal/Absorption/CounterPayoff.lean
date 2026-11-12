import YesMetaZFC.SetTheory.LargeCardinal.Absorption.CounterHeight
import YesMetaZFC.Model.Forcing.Collapse.ProductRealCollapse
import YesMetaZFC.SetTheory.InnerModel.Relative.PayoffImage
import YesMetaZFC.SetTheory.InnerModel.Relative.TruthImage

/-! # 原反例收益在高派生模型中的实际识别

背景坍塌识别规范实数并及其传递种子。测试壳中的层号和序数参数低于
已吸收高度，因而有实际地对象原像；相对 Jensen 递归唯一性识别整层，
再在派生模型中分离出同一收益。决定性针对这个实际收益调用。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel InnerModel.Relative Internal Descriptive Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem wd_counterexample_payoff_l (proper : Wd_proper_d I) (bad : ¬ M.SatisfiesSentence Axioms.lr_ad) :
    ∃ Ω, M.IsOmega Ω ∧ ∃ T₀ α₀ V₀ d₀ W₀ P b₀ R₀ π₀, ∃ z : Fin 23 → M.Domain,
      Rf_hull_d hZF Ω T₀ (ab_test_queries_l lr_ad_m lr_ad_closed_l) z α₀ V₀ d₀ W₀ P b₀ R₀ π₀ ∧
      M.mem Ω P ∧ ∃ y : Fin 18 → M.Domain, (∀ k, M.mem (y k) P) ∧
      y 0 = Ω ∧ Rb_reals_d P Ω (y 2) ∧ Tc_d (y 2) (y 1) ∧ Fseq_space_d I Ω Ω (y 3) ∧
      Jp_counter_d lr_payoff_m y ∧ Gs_number_d I Ω (y 3) (y 7) ∧
      ¬ Gs_det_d Ω (y 2) (y 3) (y 7) (y 8) (y 6) ∧
    ∃ D : Structure.{u}, ∃ native : D.Models ZF, ∃ e : D.Domain → M.Domain,
      Function.Injective e ∧ (∀ a x, M.mem x (e a) ↔ ∃ b, D.mem b a ∧ e b = x) ∧
    ∃ w b s T a c A : D.Domain,
      e w = Ω ∧ e b = y 2 ∧ e s = y 1 ∧ e a = y 4 ∧ e c = y 5 ∧ e A = y 6 ∧
      Lr_seed_d native w b s ∧ Fseq_space_d (kp_pair_l (ZF.modelsKP native)) w w T ∧
      Jp_d (kp_pair_l (ZF.modelsKP native)) lr_payoff_m s b a c A ∧
      Det_d (kp_pair_l (ZF.modelsKP native)) w b T A := by
  -- 依次读取背景、泛型扩张与派生模型，避免一次展开整条依赖见证列。
  obtain ⟨Ω,hw,T₀,α₀,V₀,d₀,W₀,P,b₀,R₀,π₀,z,test,hωP,y,owned,eyω,reals,seed₀,finite,data,number,_,no,
    β,height,_,c,X,R,model,theory,trans,_,high,h⟩ :=
    wd_counterexample_height_l hZFC proper bad
  obtain ⟨w,A,Q,U,σ,a,μ,ew,ea,fa,product,name,H₀,generic,same,h⟩ := h
  obtain ⟨g,k,ground,Z,S,value,tc,h⟩ := h
  obtain ⟨w',b,s,T,a',ww,bb,ss,aa,seed,finite',ha,determined⟩ := h
  let N := smdl_structure_l I (R := R) model.1.2.1
  have hN := ZFC.models_zf_l (theory.native_l I hZF hw)
  let H : N.Domain → Prop := fun p => M.mem p.val H₀
  let E := extension_l N hN Q U Q H
  have hE : E.Models ZF := preserves_zf_l (product.order_l hN) hN g
  let D := la_model_l S (ZF.models_kpi_l hE)
  have hD : D.Models ZF := la_model_zf_l S hE tc.1
  have clock : N.IsOmega w := by
    let nx : Nonempty {t // M.mem t X} := ⟨w⟩
    let ρ : Env (rt_model_l X nx) 1 := ⟨fun _ => w,fun _ => w⟩
    exact (Formula.satisfies_isOmega_iff _ .newest).mp
      ((smem_formula_l I model nx (Formula.isOmega .newest) ρ).mp
        ((Formula.satisfies_isOmega_iff ρ .newest).mpr (rt_omega_l trans nx hZF.1 w (ew.symm ▸ hw))))
  obtain ⟨_,f,_,_,fi,ff,fixed⟩ := bg_extension_l hZF model trans hN (product.order_l hN) generic
  have fw : f (k w) = Ω := (fixed w (k w) (ground w)).trans ew
  -- 规范名字的实际背景像是原测试实数族，随后的种子相等也是真实集合相等。
  have realSet : f Z = y 2 := hZF.1.eq_of_same_members _ _ (fun r =>
    (name.background_image_l hZF model trans hN clock fa product generic value f fi ff fixed r).trans (same r))
  obtain ⟨Z',value',members⟩ := name.value_l hN clock fa product g
  have eqZ : Z' = Z := qval_unique_l value' value
  subst Z'
  have functions t (ht : E.mem t Z) : Fn0_d (k w) (k w) t :=
    ((members t).mp ht).function_l hN clock fa product g k ground
  have wt : E.TransitiveSet (k w) := by
    intro u hu v hv
    apply (image_member_l f fi ff).mp
    have hu' := (image_member_l f fi ff).mpr hu
    rw [fw] at hu'
    exact fw.symm ▸ hw.transitive (ZF.modelsKP hZF) (f u) hu' (f v) ((image_member_l f fi ff).mpr hv)
  have nonempty : ∃ t, E.mem t Z := ⟨a'.val,bb ▸ ha⟩
  have seedImage := real_tc_image_l (ZF.modelsKP hE) hZF.1 f fi ff wt functions nonempty tc
  rw [realSet] at seedImage
  have seedEq : f S = y 1 := tc_unique_l hZF.1 seedImage seed₀
  let e : D.Domain → M.Domain := fun t => f t.val
  have ei : Function.Injective e := fun _ _ eq => Subtype.ext (fi eq)
  have ef : ∀ t x, M.mem x (e t) ↔ ∃ u, D.mem u t ∧ e u = x := by
    intro t x
    constructor
    · intro hx
      obtain ⟨u,hu,ux⟩ := (ff t.val x).mp hx
      exact ⟨⟨u,la_transitive_l S (ZF.models_kpi_l hE) tc.1 t.property hu⟩,hu,ux⟩
    · rintro ⟨u,hu,ux⟩
      exact (ff t.val x).mpr ⟨u.val,hu,ux⟩
  have eω : e w' = Ω := (congrArg f ww).trans fw
  have eb : e b = y 2 := (congrArg f bb).trans realSet
  have es : e s = y 1 := (congrArg f ss).trans seedEq
  have ep : e a' = y 4 := (congrArg f aa).trans ((fixed a (k a) (ground a)).trans ea)
  -- 每个测试壳序数先成为高源中的实际地对象，再成为派生模型中的同一序数。
  have lift {α : M.Domain} (hα : M.mem α P) (oα : M.IsOrdinal α) :
      ∃ t : D.Domain, D.IsOrdinal t ∧ e t = α := by
    let u : N.Domain := ⟨α,trans β high α (height.bound α hα oα)⟩
    have fu : f (k u) = α := fixed u (k u) (ground u)
    have ofu : M.IsOrdinal (f (k u)) := fu.symm ▸ oα
    let ρ : Env E 1 := ⟨fun _ => k u,fun _ => k u⟩
    have ou : E.IsOrdinal (k u) := (KP.ord0_sat_l (ZF.modelsKP hE) ρ .newest).mp
      ((delta0_image_l f fi ff (KP.ord0_delta_l .newest) ρ).mpr
        ((KP.ord0_sat_l (ZF.modelsKP hZF) (image_env_l f ρ) .newest).mpr ofu))
    let t : D.Domain := ⟨k u,la_ordinal_l S (ZF.models_kpi_l hE) tc.1 ou⟩
    let η : Env D 1 := ⟨fun _ => t,fun _ => t⟩
    have ot : D.IsOrdinal t := (KP.ord0_sat_l (ZF.modelsKP hD) η .newest).mp
      ((la_model_delta_l S (ZF.models_kpi_l hE) tc.1 (KP.ord0_delta_l .newest) η).mpr
        ((KP.ord0_sat_l (ZF.modelsKP hE) (image_env_l (M := D) (N := E) Subtype.val η) .newest).mpr ou))
    exact ⟨t,ot,fu⟩
  obtain ⟨square,cert,_,_,row,_,_⟩ := data.check
  obtain ⟨p,hp,γ,hγ,q,hq,V,hV,pair,pc,γV,hB,hparam,hindex,define⟩ := row
  have code := ((square.codes_l hZF γ q (y 5)).mpr ⟨p,hp,pair,pc⟩).1
  have layer : Ja_d (y 1) γ V :=
    ⟨square.1.mem hγ,(rc_value_sat_l hZF.1 ..).mpr (cert.value_l γV)⟩
  obtain ⟨γ',oγ,eγ⟩ := lift (test.transitive (y 11) (owned 11) γ hγ) (square.1.mem hγ)
  obtain ⟨q',oq,eq⟩ := lift (test.transitive (y 11) (owned 11) q hq) (square.1.mem hq)
  have code' : Oc_pair_d I (e γ') (e q') (y 5) := by simpa only [eγ,eq] using code
  have layer' : Ja_d (e s) (e γ') V := by simpa only [es,eγ] using layer
  obtain ⟨c',A',present,ec,eA⟩ := jp_pull_l hD hZF e ei ef lr_payoff_closed_l oγ oq code' layer'
    (eb.symm ▸ hB) (ep.symm ▸ hparam) (eq.symm ▸ hindex) (by simpa only [eb,ep,eq] using define)
  exact ⟨Ω,hw,T₀,α₀,V₀,d₀,W₀,P,b₀,R₀,π₀,z,test,hωP,y,owned,eyω,reals,seed₀,finite,data,number,no,
    D,hD,e,ei,ef,w',b,s,T,a',c',A',eω,eb,es,ep,ec,eA,seed,finite',present,determined c' A' present⟩

end YesMetaZFC.SetTheory.LargeCardinal
