import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawGraphSyntax
import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawCopyClass
import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawConstant
import YesMetaZFC.SetTheory.LargeCardinal.Extender.LocalFormula
import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawMembershipSystem
import YesMetaZFC.Model.SetTheory.DirectedSystem.Isomorphism
import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawAgreementRead

/-! # 原关系模型之间的实际扩展器活动边

所属模型的短扩展器经共同低层作用于指定前驱。操作保存原数字坐标、
全部内部有限支撑、原测度迹、真实商极限和常值嵌入。共同图的完整前驱
与有限 κ 幂子集对应承担一致性条件；目标保持本次实际构造的原关系。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def It_payload_d (p κ L F : M.Domain) : Prop := ∃ r, KPair_d M p κ r ∧ KPair_d M r L F

theorem It_payload_d.unique_l {p κ L F κ' L' F' : M.Domain}
    (h : It_payload_d p κ L F) (g : It_payload_d p κ' L' F') : κ = κ' ∧ L = L' ∧ F = F' := by
  obtain ⟨r, hp, hr⟩ := h
  obtain ⟨s, gp, gs⟩ := g
  obtain ⟨rfl, rfl⟩ := kpair_injective_l M hp gp
  exact ⟨rfl, kpair_injective_l M hr gs⟩


def it_payload_m {d} (p κ L F : Term d) : Formula 1 d := set[d] ⟪
  ∃ r, ⌜kpair0_m⌝ₚ(⌜p⌝ₛ, ⌜κ⌝ₛ, r) ∧ ⌜kpair0_m⌝ₚ(r, ⌜L⌝ₛ, ⌜F⌝ₛ)⟫
derive_free_closed it_payload_m

theorem it_payload_sat_l (ext : Extensional M) {d} (ρ : Env M d) (p κ L F : Term d) :
    Formula.satisfies ρ (it_payload_m p κ L F) ↔ It_payload_d (p.eval ρ) (κ.eval ρ) (L.eval ρ) (F.eval ρ) := by
  simp only [it_payload_m, It_payload_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    kpair0_sat_l ext, Definitional.Term.eval_weaken]; rfl

def It_active_d (hZF : M.Models ZF) (ω c d b j p : M.Domain) : Prop :=
  let I := kp_pair_l (ZF.modelsKP hZF)
  ∃ κ ℓ F X R Y S, It_payload_d p κ ℓ F ∧ Smdl_d I c X R ∧ Smdl_d I d Y S ∧
    ∃ w z Γ k L J O Z A q V W r N T,
      It_local_d I w X R κ ℓ F ∧ Rr_layer_d I ω X R w z ∧
      Er_agree_d I ω X R κ z Γ Y S k ∧
      (∀ x, M.mem x L ↔ M.mem x X ∧ Rd_entry_d x ℓ R) ∧
      Er_graph_d I ω L X R κ ℓ F z Y S k J O Z A q V W ∧
      Di_system_d J O A q V W ∧ Di_limit_d A q V W r N T ∧ Smdl_d I b N T ∧
      Smap_d I ω d b Y N j ∧ Er_constants_d Y r j

/-- 只在已有实际传递隶属呈示时，将同一活动边的所属判断还原到背景 ω。 -/
theorem It_active_d.local_mem_l (hZF : M.Models ZF) {ω c d b j p X R κ L F : M.Domain}
    (hω : M.IsOmega ω) (trans : M.TransitiveSet X)
    (model : Smem_d (kp_pair_l (ZF.modelsKP hZF)) c X R)
    (payload : It_payload_d p κ L F) (h : It_active_d hZF ω c d b j p) :
    It_local_d (kp_pair_l (ZF.modelsKP hZF)) ω X R κ L F := by
  obtain ⟨κ₀, L₀, F₀, X₀, R₀, _, _, pay, mx, _, w, z, _, _, _, _, _, _, _, _, _, _, _, _, _, loc, numbers, _⟩ := h
  obtain ⟨rfl, rfl, rfl⟩ := pay.unique_l payload
  obtain ⟨rfl, rfl⟩ := smdl_unique_l (kp_pair_l (ZF.modelsKP hZF)) mx model.1
  obtain ⟨rfl, _⟩ := numbers.omega_mem_l (kp_pair_l (ZF.modelsKP hZF)) (ZF.modelsKP hZF) hω trans model
  exact loc

def it_active_m {d} (ω c a b j p : Term d) : Formula 1 d := set[d] ⟪∃ κ ℓ F X R Y S,
  ⌜it_payload_m⌝ₚ(⌜p⌝ₛ, κ, ℓ, F) ∧ ⌜smdl_m (𝒞 := kpair_convention_l)⌝ₚ(⌜c⌝ₛ, X, R) ∧
  ⌜smdl_m (𝒞 := kpair_convention_l)⌝ₚ(⌜a⌝ₛ, Y, S) ∧
  (∃ w z Γ k L J O Z A q V W r N T,
    ⌜it_local_m⌝ₚ(w, X, R, κ, ℓ, F) ∧ ⌜rr_layer_m⌝ₚ(⌜ω⌝ₛ, X, R, w, z) ∧
    ⌜er_agree_m⌝ₚ(⌜ω⌝ₛ, X, R, κ, z, Γ, Y, S, k) ∧
    (∀ x, x ∈ L ↔ x ∈ X ∧ ⌜rd_entry0_m⌝ₚ(x, ℓ, R)) ∧
    ⌜er_graph_m⌝ₚ(⌜ω⌝ₛ, L, X, R, κ, ℓ, F, z, Y, S, k, J, O, Z, A, q, V, W) ∧
    ⌜di_system_m⌝ₚ(J, O, A, q, V, W) ∧ ⌜di_limit_m⌝ₚ(A, q, V, W, r, N, T) ∧
    ⌜smdl_m (𝒞 := kpair_convention_l)⌝ₚ(⌜b⌝ₛ, N, T) ∧
    ⌜smap_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ, ⌜a⌝ₛ, ⌜b⌝ₛ, Y, N, ⌜j⌝ₛ) ∧
    ⌜er_constants_m⌝ₚ(Y, r, ⌜j⌝ₛ))⟫
derive_free_closed it_active_m

theorem it_active_sat_l (hZF : M.Models ZF) {d} (ρ : Env M d) (ω c a b j p : Term d) :
    Formula.satisfies ρ (it_active_m ω c a b j p) ↔
      It_active_d hZF (ω.eval ρ) (c.eval ρ) (a.eval ρ) (b.eval ρ) (j.eval ρ) (p.eval ρ) := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  simp only [it_active_m, It_active_d, Formula.satisfies_exists_iff,
    Formula.satisfies_conj_iff, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff, Formula.satisfies_mem_iff,
    it_payload_sat_l hZF.1, smdl_sat_l I, it_local_sat_l I, rr_layer_sat_l I hZF.1,
    rd_entry0_sat_l hZF.1, er_agree_sat_l I hZF.1,
    er_graph_sat_l I hZF.1, di_system_sat_l hZF.1, di_limit_sat_l hZF.1,
    smap_sat_l I hZF.1, er_constants_sat_l hZF.1, Definitional.Term.eval_weaken]
  rfl

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 实际坍塌超幂给出同一条原关系活动边

原商系统逐项展开，实际极限投影与坍塌图复合。目标、常值嵌入、全部
代表和载荷均保持本次已有超幂的数据，不添加待证的活动边假设。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem It_ultra_d.active_l {ω c X R d Y S κ K L F b j : M.Domain}
    (fs : Fs_read_d ω X) (mx : Smem_d I c X R) (theory : Sc_theory_d I ω X R)
    (source : Ep_source_d I ω κ K Y S) (my : Smem_d I d Y S)
    (loc : It_local_d I ω X R κ L F) (agree : Ea_agree_d ω κ X Y)
    (family : Em_source_d ω κ L Y F) (coherent : Ec_source_d I ω κ L Y F)
    (ultra : It_ultra_d I ω κ L F d b j) :
    ∃ p, It_payload_d p κ L F ∧ It_active_d hZF ω c d b j p := by
  have actual := loc
  obtain ⟨_, hκ, hL, hF, _⟩ := actual
  obtain ⟨z, Γ, k, numbers, agreement, zs, _, ks⟩ := agree.raw_l hZF fs
    (source.omega.transitive (ZF.modelsKP hZF)) mx my source.transitive hκ source.cardinal_mem
  obtain ⟨Y', S', N, W, J, O, Z, A, q, V, T, r, a, C, U, i, e,
    my', target, system, limit, quotient, _, bij, he, _, constants, hj, comp⟩ := ultra
  obtain ⟨eY, eS⟩ := smdl_unique_l I my'.1 my.1
  subst Y' S'
  have graph := system.toEp_graph_d.raw_l hZF fs mx theory source my hκ hL hF numbers zs agreement
    (fun x y h => ((ks x y).mp h).2) family coherent
  have fe := fn0_of_function_l (ZF.modelsKP hZF) bij.1.1
  obtain ⟨r', cr⟩ := cp0_exists_l (ZF.modelsKP hZF) limit.projection fe
  have rs u v : Rd_entry_d u v r' ↔ M.mem u A ∧ ∃ x, Rd_entry_d u x r ∧ Rd_entry_d x v e := by
    constructor
    · intro huv
      have hu := (cr.1.bound_l huv).1
      obtain ⟨x, _, hux⟩ := limit.projection.2.1 u hu
      exact ⟨hu, x, hux, (cr.value_l limit.projection fe hux).mp huv⟩
    · rintro ⟨_, x, hux, hxv⟩
      exact (cr.value_l limit.projection fe hux).mpr hxv
  have final := di_limit_iso_l (ZF.modelsKP hZF) limit bij cr.1 rs target.1.2.2
    (fun _ _ _ _ hx hy => he.relation_l I hZF source.omega quotient target.1 hx hy)
  obtain ⟨s, hs⟩ := (I).total L F
  obtain ⟨p, hp⟩ := (I).total κ s
  have payload : It_payload_d p κ L F := ⟨s, hp, hs⟩
  refine ⟨p, payload, κ, L, F, X, R, Y, S, payload, mx.1, my.1,
    ω, z, Γ, k, L, J, O, Z, A, q, V, T, r', N, W, loc, numbers, agreement,
    ?_, graph, system.diagram, final, target.1, hj, ?_⟩
  · intro x
    exact ⟨fun hx => ⟨fs.transitive L hL x hx, (mx.2 x L).mpr ⟨fs.transitive L hL x hx, hL, hx⟩⟩,
      fun h => ((mx.2 x L).mp h.2).2.2⟩
  · intro x E hxE
    obtain ⟨B, hxB, hBE⟩ := (comp.2 x E).mp hxE
    obtain ⟨u, a, H, f, D, _, ff, fc, hf, pu, huB⟩ := constants x B hxB
    exact ⟨a, D, f, ff.function_l source.transitive, fc, u, H, pu, hf,
      (rs u E).mpr ⟨(limit.projection.bound_l huB).1, B, huB, hBE⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 给定活动系统及其隶属目标读取

完整共同图先还原为恒等，原商系统逐项读取为同一个实际系统，目标仍保留原关系。
若目标另有实际传递隶属呈示，其恒等图就是坍塌；原常值图、目标及活动边均保持不变。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 原常值代表确实属于同一分量的源内函数族，无需另给测度族或幂集假设。 -/
private theorem er_constants_mem_l {ω κ K L Y S F J O Z A p V W r N T j : M.Domain}
    (source : Ep_source_d I ω κ K Y S) (system : Ep_system_d I ω κ L Y S F J O Z A p V W)
    (limit : Di_limit_d A p V W r N T) (constants : Er_constants_d Y r j) : Ep_constants_d Y r j := by
  intro x E hxE
  obtain ⟨a,D,f,ff,fc,u,B,pair,hf,huE⟩ := constants x E hxE
  obtain ⟨c,C,Q,ha,component,model,hBC⟩ := ep_at_model_l hZF system.components
    (system.toEp_graph_d.at_l (limit.projection.bound_l huE).1 pair)
  obtain ⟨n,D',U,G,q,C',Q',hn,_,space,_,functions,quotient⟩ := component
  obtain ⟨eqC,eqQ⟩ := smdl_unique_l I quotient.code model
  subst C' Q'
  obtain ⟨g,hgB⟩ := (quotient.map.range B).mp hBC
  have hfG := (((quotient.map.classes g B).mp hgB).2 f).mp hf
  have own := (functions f).mp hfG.1
  have eq := ff.domain_eq_l hZF.1 own.2
  subst D'
  exact ⟨u,a,B,f,D,source.space_mem_l hZF hn space,source.function_l hZF own.1 own.2,fc,hf,pair,huE⟩

/-- 原后继只需其给定关系码；先读取同一系统及原常值嵌入，不预设后继良基。 -/
theorem It_active_d.system_l {ω c d b j p κ ℓ F X R Y S K K' : M.Domain}
    (owner : Ep_source_d I ω ω K X R) (parent : Ep_source_d I ω ω K' Y S)
    (mx : Smem_d I c X R) (my : Smem_d I d Y S)
    (payload : It_payload_d p κ ℓ F) (active : It_active_d hZF ω c d b j p) :
    It_local_d I ω X R κ ℓ F ∧ Ea_agree_d ω κ X Y ∧
      ∃ K₀ J O Z A q V W r N T, Ep_source_d I ω κ K₀ Y S ∧
        Ep_system_d I ω κ ℓ Y S F J O Z A q V W ∧ Di_limit_d A q V W r N T ∧
        Smdl_d I b N T ∧ Smap_d I ω d b Y N j ∧ Ep_constants_d Y r j := by
  obtain ⟨κ₀,ℓ₀,F₀,X₀,R₀,Y₀,S₀,pay,mx₀,my₀,w,z,Γ,k,L,J,O,Z₁,A,q,V,W,r,N,T₀,
    loc,numbers,agreement,length,graph,diagram,limit,model,embed,constants⟩ := active
  obtain ⟨eqκ,eqℓ,eqF⟩ := pay.unique_l payload
  subst κ₀ ℓ₀ F₀
  obtain ⟨eqX,eqR⟩ := smdl_unique_l I mx₀ mx.1
  subst X₀ R₀
  obtain ⟨eqY,eqS⟩ := smdl_unique_l I my₀ my.1
  subst Y₀ S₀
  obtain ⟨sameω,digits⟩ := numbers.omega_mem_l I (ZF.modelsKP hZF) owner.omega owner.transitive mx
  subst w
  have zs n m : Rd_entry_d n m z ↔ M.mem n ω ∧ n = m :=
    (digits n m).trans (and_congr_right fun _ => eq_comm)
  have identity := agreement.identity_l hZF mx my owner.transitive parent.transitive
  have agree := agreement.mem_l hZF (owner.read_source_l hZF) mx my parent.transitive zs
  have locality := loc
  obtain ⟨hw,hκ,hℓ,hF,_⟩ := locality
  have eqL : L = ℓ := hZF.1.eq_of_same_members L ℓ (fun x => (length x).trans
    ⟨fun h => ((mx.2 x ℓ).mp h.2).2.2,fun hx =>
      ⟨owner.transitive ℓ hℓ x hx,(mx.2 x ℓ).mpr ⟨owner.transitive ℓ hℓ x hx,hℓ,hx⟩⟩⟩)
  subst L
  obtain ⟨κ',hκY,point⟩ := agreement.injection.1.2.2 κ agreement.critical
  have eq := identity κ κ' point
  subst κ'
  have ordinal := (loc.ordinals_l (ZF.modelsKP hZF) owner.transitive ⟨c,mx⟩).1
  have data := loc
  obtain ⟨_,_,_,_,pre⟩ := (it_local_mem_l I ⟨c,mx⟩).mp data
  simp only [ex_short_m,ex_pre_m,Formula.satisfies_conj_iff,Formula.satisfies_mem_iff] at pre
  obtain ⟨K₀,source⟩ := parent.rebase_l hκY (ordinal.transitive ω pre.1.2.2.1)
    (sc_ordinal_small_l hZF owner.omega parent.transitive my parent.theory hκY ordinal)
  have system := graph.mem_system_l hZF (owner.read_source_l hZF) mx my owner.theory source
    hκ hℓ hF numbers zs agreement identity loc diagram
  have values := er_constants_mem_l hZF source system limit constants
  exact ⟨loc,agree,K₀,J,O,Z₁,A,q,V,W,r,N,T₀,source,system,limit,model,embed,values⟩

/-- 只读取已有的三个实际呈示；恒等坍塌保留原目标与同一条常值嵌入。 -/
theorem It_active_d.read_l {ω c d b j p κ ℓ F X R Y S Z T K K' : M.Domain}
    (owner : Ep_source_d I ω ω K X R) (parent : Ep_source_d I ω ω K' Y S)
    (mx : Smem_d I c X R) (my : Smem_d I d Y S) (mt : Smem_d I b Z T)
    (zt : M.TransitiveSet Z) (payload : It_payload_d p κ ℓ F) (active : It_active_d hZF ω c d b j p) :
    It_local_d I ω X R κ ℓ F ∧ Ea_agree_d ω κ X Y ∧ It_ultra_d I ω κ ℓ F d b j := by
  obtain ⟨loc,agree,K₀,J,O,Z₁,A,q,V,W,r,N,T₀,source,system,limit,model,embed,values⟩ :=
    active.system_l hZF owner parent mx my payload
  obtain ⟨eqN,eqT⟩ := smdl_unique_l I model mt.1
  subst N T₀
  obtain ⟨e,emap,es⟩ := smap_identity_l I hZF (X := Z) (c := b) owner.omega
  have bij : M.IsSetBijectionFromTo I e Z Z :=
    ⟨emap.1,fun x hx => ⟨x,hx,(es x x).mpr ⟨hx,rfl⟩⟩⟩
  have collapse : Wc_graph_d Z T e := by
    refine ⟨emap.1.1.1.1,?_⟩
    intro x y hxy
    obtain ⟨hx,rfl⟩ := (es x y).mp hxy
    refine ⟨hx,(fun v hv _ => ⟨v,(es v v).mpr ⟨hv,rfl⟩⟩),?_⟩
    intro v
    constructor
    · intro vx
      have hv := zt x hx v vx
      exact ⟨v,hv,(mt.2 v x).mpr ⟨hv,hx,vx⟩,(es v v).mpr ⟨hv,rfl⟩⟩
    · rintro ⟨u,_,ux,uv⟩
      exact ((es u v).mp uv).2 ▸ ((mt.2 u x).mp ux).2.2
  have comp : It_comp_d j e j := ⟨embed.1.1.1.1,fun x y =>
    ⟨fun h => ⟨y,h,(es y y).mpr ⟨embed.1.1.output_mem_of_pairMember h,rfl⟩⟩,
      fun ⟨v,hxv,hvy⟩ => ((es v y).mp hvy).2 ▸ hxv⟩⟩
  exact ⟨loc,agree,Y,S,Z,T,J,O,Z₁,A,q,V,W,r,b,Z,T,j,e,
    my,mt,system,limit,mt.1,collapse,bij,emap,embed,values,embed,comp⟩

end YesMetaZFC.SetTheory.LargeCardinal
