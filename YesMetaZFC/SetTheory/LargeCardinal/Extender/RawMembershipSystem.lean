import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawAgreementRead
import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawGraphSyntax
import YesMetaZFC.SetTheory.LargeCardinal.Extender.Ultrapower

/-! # 原关系坐标图与实际隶属源的同一投影

有限支撑、有限幂及坐标投影都保留原集合。规范性随后将任意原关系
坐标见证识别为这一张实际投影，故商过渡仍作用于全部原代表。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}
section Coordinates
variable (hKP : M.Models KP)
local notation "I" => kp_pair_l hKP

theorem er_coord_mem_l {ω c X R κ L z m n q a b D E t : M.Domain}
    (fs : Fs_read_d ω X) (mx : Smem_d I c X R) (hκ : M.mem κ X) (hL : M.mem L X)
    (zs : ∀ s x, Rd_entry_d s x z ↔ M.mem s ω ∧ s = x)
    (hm : M.mem m ω) (hn : M.mem n ω) (fq : Fn0_d m n q) (fb : Fn0_d n L b)
    (factor : Cp0_d m n L q b a) (ds : Ep_space_d κ m D) (es : Ep_space_d κ n E)
    (hd : M.mem D X) (he : M.mem E X) (ht : M.mem t X) (ft : Fn0_d E D t)
    (ts : ∀ s r, Rd_entry_d s r t ↔ M.mem s E ∧ Cp0_d m n κ q s r) :
    Er_coord_d I ω L X R κ L z a b D E t := by
  let nz : Nonempty {x // M.mem x X} := ⟨⟨t, ht⟩⟩
  let N := rt_model_l X nz
  have hmX := fs.transitive ω fs.omega_mem m hm
  have hnX := fs.transitive ω fs.omega_mem n hn
  have ha := fs.functions m L a hm (fs.transitive L hL) factor.1
  have hb := fs.functions n L b hn (fs.transitive L hL) fb
  have hq := fs.functions m n q hm (fs.transitive n hnX) fq
  have native : Er_native_d (M := N) ⟨κ, hκ⟩ ⟨L, hL⟩ ⟨a, ha⟩ ⟨b, hb⟩ ⟨D, hd⟩ ⟨E, he⟩ ⟨t, ht⟩ := by
    refine ⟨⟨m, hmX⟩, ⟨n, hnX⟩, ⟨q, hq⟩,
      (rt_fn_l fs.transitive nz hKP.1 ..).mpr factor.1,
      (rt_fn_l fs.transitive nz hKP.1 ..).mpr fb,
      (rt_fn_l fs.transitive nz hKP.1 ..).mpr fq,
      (rt_cp_l fs.transitive nz hKP.1 ..).mpr factor, ?_, ?_,
      (rt_fn_l fs.transitive nz hKP.1 ..).mpr ft, ?_⟩
    · exact fun s => (ds s.val).trans (rt_fn_l fs.transitive nz hKP.1 ⟨m, hmX⟩ ⟨κ, hκ⟩ s).symm
    · exact fun s => (es s.val).trans (rt_fn_l fs.transitive nz hKP.1 ⟨n, hnX⟩ ⟨κ, hκ⟩ s).symm
    · exact fun s r => (rt_entry_l fs.transitive nz hKP.1 s r ⟨t, ht⟩).trans ((ts s.val r.val).trans
        (and_congr_right fun _ => (rt_cp_l fs.transitive nz hKP.1 ⟨m, hmX⟩ ⟨n, hnX⟩ ⟨κ, hκ⟩ ⟨q, hq⟩ s r).symm))
  let ρ : Env N 7 := ⟨Fin.cases ⟨t, ht⟩ (Fin.cases ⟨E, he⟩ (Fin.cases ⟨D, hd⟩
    (Fin.cases ⟨b, hb⟩ (Fin.cases ⟨a, ha⟩ (Fin.cases ⟨L, hL⟩ (fun _ => ⟨κ, hκ⟩)))))), fun _ => ⟨t, ht⟩⟩
  have ext := (rf_ext_mem_l I hKP.1 fs.transitive mx).native_l I ⟨t, ht⟩
  have tr := smem_formula_l I mx nz (er_native_m (.bound 6) (.bound 5) (.bound 4) (.bound 3)
    (.bound 2) (.bound 1) .newest) ρ
  have raw := (er_native_sat_l ext ..).mp (tr.mp
    ((er_native_sat_l (rt_model_ext_l hKP.1 fs.transitive nz) ρ (.bound 6) (.bound 5) (.bound 4)
      (.bound 3) (.bound 2) (.bound 1) .newest).mpr native))
  have code {n f} (hn : M.mem n ω) (hf : M.mem f X) (fn : Fn0_d n L f) :
      Rr_finite_d I ω L X R z f f := by
    refine ⟨n, n, hn, fn, (zs n n).mpr ⟨hn, rfl⟩,
      (rf_fun_mem_l I hKP.1 fs.transitive mx (fs.transitive ω fs.omega_mem n hn)).mpr ⟨hf, L, hL, fn⟩, ?_⟩
    intro s x y hsx
    obtain ⟨_, rfl⟩ := (zs s x).mp hsx
    exact (rf_val_mem_l I hKP.1 fs.transitive mx hf).symm
  have carrier {A} (hA : M.mem A X) x : M.mem x A ↔ M.mem x X ∧ Rd_entry_d x A R :=
    ⟨fun hx => ⟨fs.transitive A hA x hx, (mx.2 x A).mpr ⟨fs.transitive A hA x hx, hA, hx⟩⟩,
      fun h => ((mx.2 x A).mp h.2).2.2⟩
  exact Er_coord_d.of_native_l I ⟨t, ht⟩ ext ⟨κ, hκ⟩ ⟨L, hL⟩ ⟨a, ha⟩ ⟨b, hb⟩ ⟨D, hd⟩ ⟨E, he⟩ ⟨t, ht⟩
    (code hm ha factor.1) (code hn hb fb) raw (carrier hd) (carrier he) ft
    (fun s r => (rf_val_mem_l I hKP.1 fs.transitive mx ht).symm.trans (rf_val_native_l I ⟨t, ht⟩ ext s r ⟨t, ht⟩))

end Coordinates

/-- 坐标拉回的逐值方程就是同一实际投影图上的复合。 -/
theorem Ep_pull_d.graph_l (ext : Extensional M) {κ Y m n q D E t f g : M.Domain}
    (h : Ep_pull_d κ Y m n q f g) (ds : Ep_space_d κ m D) (es : Ep_space_d κ n E)
    (ft : Fn0_d E D t) (ts : ∀ s r, Rd_entry_d s r t ↔ M.mem s E ∧ Cp0_d m n κ q s r) :
    Cp0_d E D Y t f g := by
  refine ⟨h.2.1.at_l ext es, fun s hs => ?_⟩
  obtain ⟨r, hr, hsr⟩ := ft.2.1 s hs
  obtain ⟨x, hx, hrx⟩ := (h.1.at_l ext ds).2.1 r hr
  exact ⟨r, hr, x, hx, hsr, hrx, (h.2.2 s r ((es s).mp hs) ((ts s r).mp hsr).2 x).mpr hrx⟩

section Arrows
variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 任意支撑过渡均由原源内的一张坐标投影实现，并逐代表保持旧箭头关系。 -/
theorem er_arrow_mem_l {ω c X R κ L z w Y m n q a b : M.Domain}
    (hω : M.IsOmega ω) (fs : Fs_read_d ω X) (mx : Smem_d I c X R)
    (theory : Sc_theory_d I ω X R) (hκ : M.mem κ X) (hL : M.mem L X)
    (numbers : Rr_layer_d I ω X R w z)
    (zs : ∀ s x, Rd_entry_d s x z ↔ M.mem s ω ∧ s = x)
    (hm : M.mem m ω) (hn : M.mem n ω) (fq : Fn0_d m n q) (fb : Fn0_d n L b)
    (inj : ∀ i j x, Rd_entry_d i x b → Rd_entry_d j x b → i = j) (factor : Cp0_d m n L q b a) :
    ∃ D E t, Er_coord_d I ω L X R κ L z a b D E t ∧
      (∀ B C, Er_arrow_d I ω L X R κ L z Y a b B C ↔ Ep_arrow_d ω κ L Y a b B C) ∧
      ∀ f g, Ep_pull_d κ Y m n q f g → Cp0_d E D Y t f g := by
  obtain ⟨D, hd, ds⟩ := fs.spaces κ m hκ hm
  obtain ⟨E, he, es⟩ := fs.spaces κ n hκ hn
  have hmX := fs.transitive ω fs.omega_mem m hm
  have hnX := fs.transitive ω fs.omega_mem n hn
  have hqX := fs.functions m n q hm (fs.transitive n hnX) fq
  obtain ⟨t, ht, ft, ts⟩ := sc_reindex_l hZF hω fs.transitive mx theory hmX hnX hκ hqX he fq ds es
  have coord := er_coord_mem_l (ZF.modelsKP hZF) fs mx hκ hL zs hm hn fq fb factor ds es hd he ht ft ts
  have ext := (rf_ext_mem_l I hZF.1 fs.transitive mx).native_l I ⟨w, numbers.member⟩
  refine ⟨D, E, t, coord, fun B C => ⟨?_, ?_⟩,
    fun f g pull => pull.graph_l hZF.1 ds es ft ts⟩
  · rintro ⟨D', E', t', f, g, hc, ff, hf, hg, comp⟩
    obtain ⟨rfl, rfl, rfl⟩ := hc.unique_l hZF numbers ext ⟨κ, hκ⟩ ⟨L, hL⟩ (fs.transitive L hL) inj coord
    exact ⟨m, n, q, f, g, hm, hn, fq, fb, factor, hf, hg, ep_pull_of_comp_l ds es ft ff ts comp⟩
  · rintro ⟨m', n', q', f, g, _, _, fq', fb', factor', hf, hg, pull⟩
    have eq := factor'.1.domain_eq_l hZF.1 factor.1
    subst m'
    have eq := fb'.domain_eq_l hZF.1 fb
    subst n'
    have eq := ec_factor_unique_l hZF.1 inj fq' fq factor' factor
    subst q'
    exact ⟨D, E, t, f, g, coord, pull.1.at_l hZF.1 ds, hf, hg, pull.graph_l hZF.1 ds es ft ts⟩

end Arrows
end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 给定原关系系统在真实隶属源上的完整读取

每个已有分量的完整坐标和代表族直接按两端真实隶属关系读取，原商模型码保持原值。
坐标投影由唯一性识别，全部代表的拉回方程随之成为原隶属系统的代表方程。
模型表、指标序、标号节点和两张关系图均保留原值。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Er_graph_d.mem_system_l
    {ω c X R d Y S κ K L F w z Γ k J O Z A p V W : M.Domain}
    (graph : Er_graph_d I ω L X R κ L F z Y S k J O Z A p V W)
    (fs : Fs_read_d ω X) (mx : Smem_d I c X R) (my : Smem_d I d Y S)
    (theory : Sc_theory_d I ω X R) (parent : Ep_source_d I ω κ K Y S)
    (hκ : M.mem κ X) (hL : M.mem L X) (hF : M.mem F X)
    (numbers : Rr_layer_d I ω X R w z)
    (zs : ∀ n m, Rd_entry_d n m z ↔ M.mem n ω ∧ n = m)
    (agree : Er_agree_d I ω X R κ z Γ Y S k)
    (identity : ∀ x y, Rd_entry_d x y k → x = y)
    (locality : It_local_d I w X R κ L F) (diagram : Di_system_d J O A p V W) :
    Ep_system_d I ω κ L Y S F J O Z A p V W := by
  have ew := (numbers.omega_mem_l I (ZF.modelsKP hZF) parent.omega fs.transitive mx).1
  have locality : It_local_d I ω X R κ L F := ew ▸ locality
  let N := smdl_structure_l I (R := R) ⟨w,numbers.member⟩
  have ext := (rf_ext_mem_l I hZF.1 fs.transitive mx).native_l I ⟨w,numbers.member⟩
  let ξ : N.Domain := ⟨κ,hκ⟩
  have bound {a U n D : M.Domain} (au : Rd_entry_d a U F) (fa : Fn0_d n L a)
      (space : Ep_space_d κ n D) : ∀ B, M.mem B U → M.MemberSubset B D := by
    obtain ⟨hw,_,_,_,valid⟩ := (it_local_mem_l I ⟨c,mx⟩).mp locality
    let nx : Nonempty {x // M.mem x X} := ⟨⟨ω,hw⟩⟩
    have en := rt_model_ext_l hZF.1 fs.transitive nx
    simp only [ex_short_m,ex_pre_m,Formula.satisfies_conj_iff] at valid
    have measures := (em_family_sat_l en _ _ _ _ _).mp valid.1.2.2.2.2.2.2.1
    have auX := rd_entry_transitive_l fs.transitive hF au
    obtain ⟨m,E,hm,fm,es,ultra⟩ := measures.measure ⟨a,auX.1⟩ ⟨U,auX.2⟩
      ((rt_entry_l fs.transitive nx hZF.1 ..).mpr au)
    have fm := (rt_fn_l fs.transitive nx hZF.1 ..).mp fm
    have eq := fm.domain_eq_l hZF.1 fa
    have es : Ep_space_d κ m.val E.val := by
      intro s
      constructor
      · intro hs
        exact (rt_fn_l fs.transitive nx hZF.1 ..).mp
          ((es ⟨s,fs.transitive E.val E.property s hs⟩).mp hs)
      · intro hs
        exact (es ⟨s,fs.functions m.val κ s hm (fs.transitive κ hκ) hs⟩).mpr
          ((rt_fn_l fs.transitive nx hZF.1 ..).mpr hs)
    have es : Ep_space_d κ n E.val := eq ▸ es
    have same := hZF.1.eq_of_same_members E.val D (fun s => (es s).trans (space s).symm)
    intro B hB x hx
    have hBX := fs.transitive U auX.2 B hB
    exact same ▸ ultra.1.1 ⟨B,hBX⟩ hB ⟨x,fs.transitive B hBX x hx⟩ hx
  have components a o (ho : Rd_entry_d a o Z) : Ep_component_d I ω κ L Y S F a o := by
    obtain ⟨n,m,b,d,U,D,i,t,y,V,G,q,C,T,hn,fa,nm,fb,ga,space,au,carrier,fi,ids,rt,dy,measure,functions,quotient⟩ :=
      graph.components a o ho
    have eq := ((zs n m).mp nm).2
    subst m
    have hnX := fs.transitive ω fs.omega_mem n hn
    have fb := (rf_fun_mem_l I hZF.1 fs.transitive mx hnX).mp fb
    have eq : a = b := by
      apply (fa.mono_target_l (fs.transitive L hL)).ext_l hZF.1 (fb.function_l fs.transitive)
      intro j hj
      obtain ⟨x,hx,jx⟩ := fa.2.1 j hj
      exact ⟨x,jx,(rf_val_mem_l I hZF.1 fs.transitive mx fb.1).mp
        ((ga j j x ((zs j j).mpr ⟨parent.omega.transitive (ZF.modelsKP hZF) n hn j hj,rfl⟩)).mp jx)⟩
    subst b
    obtain ⟨hd,space⟩ := (er_space_mem_l I hZF.1 fs mx hκ hn).mp space
    have eq : D = d := hZF.1.eq_of_same_members D d (fun x => (carrier x).trans
      ⟨fun hx => ((mx.2 x d).mp hx.2).2.2,
        fun hx => ⟨fs.transitive d hd x hx,(mx.2 x d).mpr ⟨fs.transitive d hd x hx,hd,hx⟩⟩⟩)
    subst d
    have eq := identity D y dy
    subst y
    have hDY := agree.injection.1.output_mem_of_pairMember dy
    have tid x y : Rd_entry_d x y t ↔ M.mem x D ∧ x = y := by
      constructor
      · intro xy
        obtain ⟨hx,hxy⟩ := (rt.2 x y).mp xy
        exact ⟨hx,identity x y hxy⟩
      · rintro ⟨hx,rfl⟩
        have low := agree.downward D x (agree.injection.1.input_mem_of_pairMember dy)
          (fs.transitive D hd x hx) ((mx.2 x D).mpr ⟨fs.transitive D hd x hx,hd,hx⟩)
        obtain ⟨y,_,xy⟩ := agree.injection.1.2.2 x low
        exact (rt.2 x x).mpr ⟨hx,(identity x y xy).symm ▸ xy⟩
    have ft : Fn0_d D Y t := fn0_of_function_l (ZF.modelsKP hZF)
      (rt.isSetFunctionFromTo agree.injection.1 (fun x hx =>
        agree.injection.1.input_mem_of_pairMember ((rt.2 x x).mp ((tid x x).mpr ⟨hx,rfl⟩)).2))
    have au := (rf_val_mem_l I hZF.1 fs.transitive mx hF).mp au
    have hU := (rd_entry_transitive_l fs.transitive hF au).2
    have trace {B} (hB : M.mem B U) : Rt_trace_d I D i R B B := by
      intro x
      have hBX := fs.transitive U hU B hB
      constructor
      · intro hx
        exact ⟨bound au fa space B hB x hx,x,(ids x x).mpr ⟨bound au fa space B hB x hx,rfl⟩,
          (mx.2 x B).mpr ⟨fs.transitive B hBX x hx,hBX,hx⟩⟩
      · rintro ⟨_,y,xy,yB⟩
        exact ((ids x y).mp xy).2 ▸ ((mx.2 y B).mp yB).2.2
    have eq : V = U := hZF.1.eq_of_same_members V U (fun B => (measure B).trans
      ⟨fun ⟨B',_,hB',tr⟩ => by
        have hB' := ((mx.2 B' U).mp hB').2.2
        exact (hZF.1.eq_of_same_members B B' (fun x => (tr x).trans (trace hB' x).symm)).symm ▸ hB',
        fun hB => ⟨B,fs.transitive U hU B hB,(mx.2 B U).mpr ⟨fs.transitive U hU B hB,hU,hB⟩,trace hB⟩⟩)
    subst V
    have decode {g} (hg : M.mem g Y) : Rc_graph_d I Y S t g g := by
      intro x y v xy
      obtain ⟨_,rfl⟩ := (tid x y).mp xy
      exact (rf_val_mem_l I hZF.1 parent.transitive my hg).symm
    have actual g : M.mem g G ↔ M.mem g Y ∧ Fn0_d D Y g := by
      constructor
      · intro hg
        obtain ⟨fg,b,fb,values⟩ := (functions g).mp hg
        have fb := (rf_fun_mem_l I hZF.1 parent.transitive my hDY).mp fb
        have eq := values.unique_l I hZF.1 ft fg (fb.function_l parent.transitive) (decode fb.1)
        exact ⟨eq.symm ▸ fb.1,fg⟩
      · rintro ⟨hg,fg⟩
        exact (functions g).mpr ⟨fg,g,(rf_fun_mem_l I hZF.1 parent.transitive my hDY).mpr
          (sc_function_domain_l (parent.algebra_l (ZF.modelsKP hZF)) hg fg),decode hg⟩
    exact ⟨n,D,U,G,q,C,T,hn,fa,space,au,actual,quotient⟩
  have arrows a b (ab : Rd_entry_d a b O) : ∀ B C,
      Er_arrow_d I ω L X R κ L z Y a b B C ↔ Ep_arrow_d ω κ L Y a b B C := by
    obtain ⟨_,hb,q,m,n,hm,hn,fq,fb,factor⟩ := (graph.order_spec a b).mp ab
    obtain ⟨_,_,_,inj⟩ := (graph.indices b).mp hb
    obtain ⟨_,_,_,_,read,_⟩ := er_arrow_mem_l hZF parent.omega fs mx theory hκ hL numbers zs
      hm hn fq fb inj factor
    exact read
  have eg : Ep_graph_d I ω κ L Y S F J O Z A p V W := {
    order := graph.order
    order_spec := graph.order_spec
    projection := graph.projection
    indices := graph.indices
    codes := graph.codes
    nodes := graph.nodes
    index := graph.index
    components := components
    relations := graph.relations
    arrows := by
      intro u v
      constructor
      · rintro huv
        obtain ⟨hu,hv,a,b,B,C,pu,pv,ab,edge⟩ := (graph.arrows u v).mp huv
        exact ⟨hu,hv,a,b,B,C,pu,pv,(arrows a b ab B C).mp edge⟩
      · rintro ⟨hu,hv,a,b,B,C,pu,pv,edge⟩
        have ha := (graph.projection.bound_l ((graph.index u a B pu).mpr hu)).2
        have hb := (graph.projection.bound_l ((graph.index v b C pv).mpr hv)).2
        have actual := edge
        obtain ⟨m,n,q,_,_,hm,hn,fq,fb,factor,_⟩ := edge
        have ab := (graph.order_spec a b).mpr ⟨ha,hb,q,m,n,hm,hn,fq,fb,factor⟩
        exact (graph.arrows u v).mpr ⟨hu,hv,a,b,B,C,pu,pv,ab,(arrows a b ab B C).mpr actual⟩ }
  refine { toEp_graph_d := eg, diagram := diagram, representatives := ?_ }
  intro u v a b B C pu pv edge g hg
  obtain ⟨hu,_,ab,_⟩ := (graph.arrow_l pu pv).mp edge
  obtain ⟨_,hb,q,m,n,hm,hn,fq,fb,factor⟩ := (graph.order_spec a b).mp ab
  obtain ⟨_,_,_,inj⟩ := (graph.indices b).mp hb
  obtain ⟨D,hD,ds⟩ := fs.spaces κ m hκ hm
  obtain ⟨E,hE,es⟩ := fs.spaces κ n hκ hn
  have hmX := fs.transitive ω fs.omega_mem m hm
  have hnX := fs.transitive ω fs.omega_mem n hn
  have hq := fs.functions m n q hm (fs.transitive n hnX) fq
  obtain ⟨t,ht,ft,ts⟩ := sc_reindex_l hZF parent.omega fs.transitive mx theory hmX hnX hκ hq hE fq ds es
  have coord := er_coord_mem_l (ZF.modelsKP hZF) fs mx hκ hL zs hm hn fq fb factor ds es hD hE ht ft ts
  obtain ⟨D',E',t',g',old,hg',comp⟩ := graph.lift_l hZF.1 pu pv edge hg
  obtain ⟨rfl,rfl,rfl⟩ := old.unique_l hZF numbers ext ξ ⟨L,hL⟩ (fs.transitive L hL) inj coord
  obtain ⟨o,C₀,S₀,ho,component,model,hB⟩ := ep_at_model_l hZF components (graph.at_l hu pu)
  obtain ⟨m',D₀,U₀,G₀,q₀,C₁,S₁,_,fa,space,_,_,quotient⟩ := component
  obtain ⟨rfl,rfl⟩ := smdl_unique_l I quotient.code model
  have fg := quotient.map.functions g (quotient.map.member_family_l I hB hg)
  have eq := fa.domain_eq_l hZF.1 factor.1
  subst m'
  exact ⟨m,n,q,g',hm,hn,fq,fb,factor,hg',
    ep_pull_of_comp_l ds es ft ((show Ep_fun_d κ Y m g from ⟨D₀,space,fg⟩).at_l hZF.1 ds) ts comp⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 实际隶属商系统的原关系实例

每个分量码、标签节点、投影和两种关系均为原系统中的同一对象。
任意支撑过渡的完整初等图及全部代表提升由已实现的分量映射产生。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ep_graph_d.raw_l {ω c X R d Y S κ K L F w z Γ k J O Z A p T V : M.Domain}
    (fs : Fs_read_d ω X) (mx : Smem_d I c X R) (theory : Sc_theory_d I ω X R)
    (source : Ep_source_d I ω κ K Y S) (my : Smem_d I d Y S)
    (hκ : M.mem κ X) (hL : M.mem L X) (hF : M.mem F X)
    (numbers : Rr_layer_d I ω X R w z)
    (zs : ∀ s x, Rd_entry_d s x z ↔ M.mem s ω ∧ s = x)
    (agree : Er_agree_d I ω X R κ z Γ Y S k)
    (identity : ∀ x y, Rd_entry_d x y k → x = y)
    (family : Em_source_d ω κ L Y F) (coherent : Ec_source_d I ω κ L Y F)
    (h : Ep_graph_d I ω κ L Y S F J O Z A p T V) :
    Er_graph_d I ω L X R κ L F z Y S k J O Z A p T V := by
  have arrow a b (hab : Rd_entry_d a b O) :
      ∀ B C, Er_arrow_d I ω L X R κ L z Y a b B C ↔ Ep_arrow_d ω κ L Y a b B C := by
    obtain ⟨_, hb, q, m, n, hm, hn, fq, fb, factor⟩ := (h.order_spec a b).mp hab
    obtain ⟨_, _, _, inj⟩ := (h.indices b).mp hb
    obtain ⟨_, _, _, _, same, _⟩ := er_arrow_mem_l hZF source.omega fs mx theory hκ hL numbers zs hm hn fq fb inj factor
    exact same
  refine ⟨h.order, h.order_spec, h.indices, h.codes,
    fun a o hao => (h.components a o hao).raw_l (ZF.modelsKP hZF) fs mx my source.transitive
      (source.algebra_l (ZF.modelsKP hZF)) hκ hL hF zs agree identity family,
    h.projection, h.nodes, h.index, ?_, h.relations, ?_⟩
  · intro u v
    constructor
    · intro huv
      obtain ⟨hu, hv, a, b, B, C, pu, pv, edge⟩ := (h.arrows u v).mp huv
      have ha := (h.projection.bound_l ((h.index u a B pu).mpr hu)).2
      have hb := (h.projection.bound_l ((h.index v b C pv).mpr hv)).2
      have actual := edge
      obtain ⟨m, n, q, _, _, hm, hn, fq, fb, factor, _⟩ := actual
      have hab := (h.order_spec a b).mpr ⟨ha, hb, q, m, n, hm, hn, fq, fb, factor⟩
      exact ⟨hu, hv, a, b, B, C, pu, pv, hab, (arrow a b hab B C).mpr edge⟩
    · rintro ⟨hu, hv, a, b, B, C, pu, pv, hab, edge⟩
      exact (h.arrows u v).mpr ⟨hu, hv, a, b, B, C, pu, pv, (arrow a b hab B C).mp edge⟩
  · intro a b hab
    obtain ⟨ha, hb, q, m, n, hm, hn, fq, fb, factor⟩ := (h.order_spec a b).mp hab
    obtain ⟨_, _, _, inj⟩ := (h.indices b).mp hb
    obtain ⟨_, hz⟩ := h.codes
    obtain ⟨o₀, _, ha₀⟩ := hz.2.1 a ha
    obtain ⟨o₁, _, hb₁⟩ := hz.2.1 b hb
    obtain ⟨j, C₀, W₀, C₁, W₁, mc₀, mc₁, _, hj, _, js, lift⟩ :=
      ep_map_l hZF source family coherent hm hn fq fb inj factor (h.components a o₀ ha₀) (h.components b o₁ hb₁)
    obtain ⟨D, E, t, coord, same, pull⟩ := er_arrow_mem_l hZF source.omega fs mx theory hκ hL numbers zs hm hn fq fb inj factor
    refine ⟨j, o₀, C₀, W₀, o₁, C₁, W₁, ha₀, hb₁, mc₀, mc₁, hj,
      fun B C => (js B C).trans (and_congr_right fun _ => and_congr_right fun _ => (same B C).symm),
      D, E, t, coord, fun B C hBC f hf => ?_⟩
    obtain ⟨g, hg, fg⟩ := lift B C hBC f hf
    exact ⟨g, hg, pull f g fg⟩

end YesMetaZFC.SetTheory.LargeCardinal
