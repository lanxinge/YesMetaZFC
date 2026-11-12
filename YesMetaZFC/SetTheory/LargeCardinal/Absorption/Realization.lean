import YesMetaZFC.SetTheory.LargeCardinal.Absorption.Limit
import YesMetaZFC.Model.SetTheory.Embedding.RankFixed
import YesMetaZFC.Model.Forcing.Ground.Ordinals
import YesMetaZFC.SetTheory.LargeCardinal.Absorption.RunClock
import YesMetaZFC.SetTheory.LargeCardinal.Absorption.Links
import YesMetaZFC.SetTheory.LargeCardinal.Absorption.ReturnedFilter
import YesMetaZFC.Model.Forcing.Ground.ProductProjection
import YesMetaZFC.Model.Forcing.Collapse.ProductRealCollapse
import YesMetaZFC.Model.SetTheory.Game.NodeEmbedding
import YesMetaZFC.Model.Forcing.Collapse.ProductQueryTop
import YesMetaZFC.SetTheory.InnerModel.Relative.TruthSyntax
import YesMetaZFC.SetTheory.InnerModel.Relative.TruthImage
import YesMetaZFC.Model.Forcing.Ground.BackgroundExtension
import YesMetaZFC.Model.Forcing.Ground.RealGround
import YesMetaZFC.SetTheory.Descriptive.Topology.Completion
import YesMetaZFC.SetTheory.LargeCardinal.Absorption.Target
import YesMetaZFC.Model.Forcing.Collapse.ProductTruthPrefix

/-! # 返回嵌入控制极限及其泛型扩张的序数高度

极限序数不超过其返回像，而原返回目标的全部序数有实际壳内界 θ。力迫不增加序数，
故扩张中的每个序数也有严格低于同一 θ 的原序数代表；不同模型载体不作字面混同。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 高度证书保留实际扩张及其规范地嵌入，不把商载体与背景集合直接等同。 -/
def Ab_extension_height_d {ω cY Y F C U d X V J σ A Q T : M.Domain}
    (lim : Ab_limit_d hZF ω cY Y F C U d X V J σ A Q T) (H θ : M.Domain) : Prop :=
  let L := smdl_structure_l I (R := V) lim.model.1.2.1
  let hL := ZFC.models_zf_l (lim.theory.native_l I hZF lim.omega)
  let q : L.Domain := ⟨Q,lim.inside.2.2.1⟩
  let t : L.Domain := ⟨T,lim.inside.2.2.2⟩
  let G : L.Domain → Prop := fun p => M.mem p.val H
  let E := extension_l L hL q t q G
  ∃ e : L.Domain → E.Domain, Function.Injective e ∧
    (∀ a, Gval_d L q t q G a (e a)) ∧
    (∀ a y, E.mem y (e a) ↔ ∃ b, L.mem b a ∧ e b = y) ∧
    ∀ ξ, E.IsOrdinal ξ → ∃ α, L.IsOrdinal α ∧ e α = ξ ∧ M.mem α.val Y ∧ M.mem α.val θ

theorem Ab_limit_d.height_l {ω cY Y S θ F C U d X V J σ A Q T : M.Domain}
    (target : Smem_d I cY Y S) (yt : M.TransitiveSet Y) (bound : Oh_bound_d Y θ)
    (lim : Ab_limit_d hZF ω cY Y F C U d X V J σ A Q T) :
    ∀ α, M.mem α X → M.IsOrdinal α → M.mem α θ := by
  intro α hα ordinal
  obtain ⟨β,hβ,image⟩ := lim.returns.1.1.2.2 α hα
  have oβ := lim.returns.ordinal_l hZF lim.omega lim.transitive yt lim.model target image ordinal
  have sub := lim.returns.ordinal_le_l hZF lim.omega lim.transitive yt lim.model target image ordinal
  exact ordinal_down_l (ZF.modelsKP hZF) ordinal bound.ordinal sub (bound.bound β hβ oβ)

theorem Ab_limit_d.extension_height_l {ω cY Y S θ F C U d X V J σ A Q T H : M.Domain}
    (target : Smem_d I cY Y S) (yt : M.TransitiveSet Y) (bound : Oh_bound_d Y θ)
    (lim : Ab_limit_d hZF ω cY Y F C U d X V J σ A Q T)
    (generic : Gset_d Q T Q X H) : Ab_extension_height_d hZF lim H θ := by
  dsimp only [Ab_extension_height_d]
  let L := smdl_structure_l I (R := V) lim.model.1.2.1
  have hL := ZFC.models_zf_l (lim.theory.native_l I hZF lim.omega)
  let q : L.Domain := ⟨Q,lim.inside.2.2.1⟩
  let t : L.Domain := ⟨T,lim.inside.2.2.2⟩
  let G : L.Domain → Prop := fun p => M.mem p.val H
  have O := lim.product.order_l hL
  have g : Generic_d L q t q G :=
    ((lim.model.generic_code_l I hZF.1 lim.transitive (ZF.modelsKP hL) q t q H).mp generic).2
  obtain ⟨b,hb⟩ := g.inhabited
  obtain ⟨e,checks,full,inj,ordinals⟩ := check_map_ordinals_l O hL g hb
  refine ⟨e,inj,fun a => (gval_check_map_l O hL g hb e checks a (e a)).mpr rfl,full,?_⟩
  intro ξ hξ
  obtain ⟨α,hα,eq⟩ := (ordinals ξ).mp hξ
  have li : Function.Injective (Subtype.val : L.Domain → M.Domain) := fun _ _ eq => Subtype.ext eq
  have ordinal := image_ord_l (M := L) (N := M) hL hZF Subtype.val li (smem_full_l I lim.model lim.transitive) hα
  exact ⟨α,hα,eq,lim.returns.ordinal_mem_l hZF lim.omega lim.transitive yt lim.model target α.property ordinal,
    lim.height_l hZF target yt bound α.val α.property ordinal⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 全部出生稠密集沿原返回图得到实际命中

源枚举行在下一行加入出生表，以后每一步运输同一表项。返回交换三角形
保证表项始终代表同一个原稠密集。公平性选出的完成行于是命中该稠密集的像。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF) {c P R : M.Domain}
  (model : Smem_d (kp_pair_l (ZF.modelsKP hZF)) c P R) (trans : M.TransitiveSet P)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
include trans

theorem Ab_run_d.birth_l {ω cY Y S : (smdl_structure_l I (R := R) model.1.2.1).Domain}
    {F b r₀ l p D E : M.Domain} {v₀ : Fin 26 → M.Domain}
    (hΩ : M.IsOmega ω.val) (run : Ab_run_d I P ω.val cY.val Y.val S.val F)
    (start : Rd_entry_d b r₀ F) (tuple₀ : Rt_tuple_d v₀ r₀)
    (pair : KPair_d M p (v₀ 14) l) (enumerated : Rd_entry_d l D (v₀ 16)) (returned : Rd_entry_d D E (v₀ 3)) :
    ∀ j r (v : Fin 26 → M.Domain), Rd_entry_d j r F → Rt_tuple_d v r → M.mem b j →
      ∃ Z, Rd_entry_d p Z (v 17) ∧ Rd_entry_d Z E (v 3) := by
  have index {i r} {v : Fin 26 → M.Domain} (ir : Rd_entry_d i r F) (vr : Rt_tuple_d v r) : v 14 = i := by
    obtain ⟨w,wr,timing⟩ := run.timing_l hZF.1 model trans ir
    exact rt_tuple_inj_l wr vr ▸ timing.index
  have hl := ((run.queues b r₀ v₀ start tuple₀).birth.enumeration.function.bound_l enumerated).1
  let ρ : Env M 4 := ⟨fun k => [F,b,p,E].get k,fun _ => F⟩
  let φ : UnarySchema 4 := { body := set[5] ⟪∀ r B σ,
    ⌜rd_entry0_m⌝ₚ(⌜(.bound 0 : Term 5)⌝ₛ,r,⌜(.bound 1 : Term 5)⌝ₛ) →
    ⌜(rt_coord_m (17 : Fin 26))⌝ₚ(r,B) → ⌜(rt_coord_m (3 : Fin 26))⌝ₚ(r,σ) →
    ⌜(.bound 2 : Term 5)⌝ₛ ∈ ⌜(.bound 0 : Term 5)⌝ₛ → ∃ Z,
      ⌜rd_entry0_m⌝ₚ(⌜(.bound 3 : Term 5)⌝ₛ,Z,B) ∧ ⌜rd_entry0_m⌝ₚ(Z,⌜(.bound 4 : Term 5)⌝ₛ,σ)⟫ }
  have read j : φ.denote ρ j ↔ ∀ r B σ, Rd_entry_d j r F → Rt_coord_d (17 : Fin 26) r B →
      Rt_coord_d (3 : Fin 26) r σ → M.mem b j → ∃ Z, Rd_entry_d p Z B ∧ Rd_entry_d Z E σ := by
    simp only [φ,UnarySchema.denote,Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,
      Formula.satisfies_mem_iff,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
      rd_entry0_sat_l hZF.1,rt_coord_sat_l hZF.1,Definitional.Term.eval_weaken]
    rfl
  have all j : φ.denote ρ j := ZF.mem_ind_l M hZF I φ ρ (by
    intro j ih
    apply (read j).mpr
    intro r B σ jr cB cσ bj
    obtain ⟨v,vr,_,ret,_⟩ := run.columns_l hZF.1 model trans jr
    have eB : v 17 = B := by
      obtain ⟨w,wr,eq⟩ := cB
      exact (congrFun (rt_tuple_inj_l vr wr) 17).trans eq
    have eσ : v 3 = σ := by
      obtain ⟨w,wr,eq⟩ := cσ
      exact (congrFun (rt_tuple_inj_l vr wr) 3).trans eq
    obtain ⟨i,hi,succ⟩ := hΩ.exists_predecessor_of_mem_of_nonempty hZF (run.function.bound_l jr).1 ⟨b,bj⟩
    obtain ⟨s,_,is⟩ := run.function.2.1 i hi
    obtain ⟨w,ws,_,oldReturn,_⟩ := run.columns_l hZF.1 model trans is
    obtain ⟨f,edge,_,_,_,_,_,_,table⟩ := run.step_links_l hZF.1 model trans succ is jr ws vr
    have keep := run.keep_l hZF.1 model trans succ is jr ws vr
    have hist := run.histories j r v jr vr
    have square := hist.returns.comp_l hZF hist.diagram (fun _ h => h) edge (keep.2.2 i (w 3) oldReturn) ret
    have input : ∃ Z, ((M.mem (v₀ 14) (w 14) ∧ Rd_entry_d p Z (w 17)) ∨
        (v₀ 14 = w 14 ∧ Rd_entry_d l Z (w 16))) ∧ Rd_entry_d Z E (w 3) := by
      rcases (succ b).mp bj with bi | eq
      · obtain ⟨Z,pZ,ZE⟩ := (read i).mp (ih i succ.predecessor_mem) s (w 17) (w 3) is
          ⟨w,ws,rfl⟩ ⟨w,ws,rfl⟩ bi
        exact ⟨Z,Or.inl ⟨(index start tuple₀).symm ▸ (index is ws).symm ▸ bi,pZ⟩,ZE⟩
      · have eq := hZF.1.eq_of_same_members b i eq
        have sr := (fn0_function_l (ZF.modelsKP hZF) run.function).1.2 i s r₀ is (eq ▸ start)
        have ew := rt_tuple_inj_l ws (sr.symm ▸ tuple₀)
        exact ⟨D,Or.inr ⟨congrFun ew 14 |>.symm,congrFun ew 16 |>.symm ▸ enumerated⟩,
          congrFun ew 3 |>.symm ▸ returned⟩
    obtain ⟨Z,value,ZE⟩ := input
    obtain ⟨Z',ZZ',Z'E⟩ := (square.2 Z E).mp ZE
    exact ⟨Z',eB ▸ (table p Z').mpr ⟨v₀ 14,l,Z,pair,hl,value,ZZ'⟩,eσ ▸ Z'E⟩) j
  exact fun j r v jr vr bj => (read j).mp (all j) r (v 17) (v 3) jr ⟨v,vr,rfl⟩ ⟨v,vr,rfl⟩ bj

/-- 背景中的任意出生稠密集都由完整枚举登记，公平调度命中其同一返回像。 -/
theorem Ab_run_d.dense_hit_l {ω cY Y S : (smdl_structure_l I (R := R) model.1.2.1).Domain}
    {F b r₀ D : M.Domain} {v₀ : Fin 26 → M.Domain}
    (hΩ : M.IsOmega ω.val) (run : Ab_run_d I P ω.val cY.val Y.val S.val F)
    (start : Rd_entry_d b r₀ F) (tuple₀ : Rt_tuple_d v₀ r₀)
    (inside : M.mem D (v₀ 1)) (dense : Dense_set_d M (v₀ 5) (v₀ 6) (v₀ 5) D) :
    ∃ j r, ∃ v : Fin 26 → M.Domain, ∃ E,
      M.mem b j ∧ Rd_entry_d j r F ∧ Rt_tuple_d v r ∧
      Rd_entry_d D E (v₀ 3) ∧ Rd_entry_d (v 19) E (v 3) ∧ v 7 = v 20 ∧
      M.mem (v 21) (v 19) ∧ M.mem (v 21) (v 11) := by
  have source := run.queues b r₀ v₀ start tuple₀
  have hD := (source.birth.family.members D).mpr ⟨inside,dense⟩
  obtain ⟨l,hl,enumerated⟩ := source.birth.enumeration.onto D inside
    ((source.frame.model.2 D (v₀ 15)).mpr ⟨inside,source.birth.family.inside,hD⟩)
  have hb := source.birth.history.natural
  obtain ⟨k,code⟩ := oc_pair_exists_l I hZF (hΩ.members_areOrdinals (ZF.modelsKP hZF) _ hb)
    (hΩ.members_areOrdinals (ZF.modelsKP hZF) _ hl)
  have hk := oc_pair_natural_l I hZF hΩ hb hl code
  obtain ⟨p,pair⟩ := (I).total (v₀ 14) l
  obtain ⟨E,_,returned⟩ := source.frame.returns.1.1.2.2 D inside
  obtain ⟨j,r,v,jr,vr,cursor,finished,hit,accepted⟩ := run.fair_l hZF model trans hΩ k hk
  have state := run.queues j r v jr vr
  have kt : M.mem k (v 14) := cursor ▸ (state.done finished).1
  have bt := ordinal_down_l (ZF.modelsKP hZF)
    (hΩ.members_areOrdinals (ZF.modelsKP hZF) _ hb)
    (hΩ.members_areOrdinals (ZF.modelsKP hZF) _ state.birth.history.natural)
    (oc_pair_left_bound_l I hZF hΩ hb hl code) kt
  obtain ⟨a,ar,old⟩ := run.timing_l hZF.1 model trans start
  obtain ⟨w,wr,now⟩ := run.timing_l hZF.1 model trans jr
  have ib := rt_tuple_inj_l ar tuple₀ ▸ old.index
  have ij := rt_tuple_inj_l wr vr ▸ now.index
  have bj : M.mem b j := ib ▸ ij ▸ bt
  obtain ⟨Z,pZ,ZE⟩ := run.birth_l hZF model trans hΩ start tuple₀ pair enumerated returned j r v jr vr bj
  have selected := state.pick (v₀ 14) l p hb hl (cursor.symm ▸ code) pair
  have picked : Rd_entry_d p (v 19) (v 17) := selected.elim And.right
    (fun h => (KP.mem_irrefl_d (ZF.modelsKP hZF) _ (h.1 ▸ bt)).elim)
  obtain ⟨C,_,table⟩ := state.birth.history.table
  have eq := (fn0_function_l (ZF.modelsKP hZF) table).1.2 p Z (v 19) pZ picked
  exact ⟨j,r,v,E,bj,jr,vr,returned,eq ▸ ZE,finished,hit,accepted⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 公平吸收调度产生直接极限上的全乘积泛型

极限锥覆盖全部稠密参数。把任意稠密集回收到真实出生行，公平调度给出
原像任务的命中；返回因子的单射性将同一命中读回极限。滤子来自原前缀
条件的有向生成族，未另选一个无关泛型。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Model.Forcing.Internal
universe u
def Ab_generic_d {M : Structure.{u}} (hZF : M.Models ZF) (P ω cY Y F : M.Domain) : Prop :=
  ∃ C U H₀ d X V J σ A Q T H, Ab_return_order_d F C U ∧ Ab_filter_d F C U H₀ ∧
    ∃ lim : Ab_limit_d hZF ω cY Y F C U d X V J σ A Q T,
    Gset_d Q T Q X H ∧ (∀ p, M.mem p H ↔ M.mem p Q ∧ ∃ z, Rd_entry_d p z σ ∧ M.mem z H₀) ∧
    ∃ B Z θ, M.mem B P ∧ M.mem Z P ∧ M.mem B Y ∧ M.mem Z Y ∧ Rb_reals_d P ω B ∧ Tc_d B Z ∧ M.mem θ P ∧ Oh_bound_d Y θ ∧
      (∀ α, M.mem α X → M.IsOrdinal α → M.mem α θ) ∧ Ab_extension_height_d hZF lim H θ

variable {M : Structure.{u}} (hZF : M.Models ZF) {c P R : M.Domain}
  (model : Smem_d (kp_pair_l (ZF.modelsKP hZF)) c P R) (trans : M.TransitiveSet P)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
include trans

theorem Ab_limit_d.generic_l {ω cY Y S C U : (smdl_structure_l I (R := R) model.1.2.1).Domain}
    {F d X V J σ A Q T H₀ : M.Domain}
    (run : Ab_run_d I P ω.val cY.val Y.val S.val F) (ctx : Ab_return_order_d F C.val U.val)
    (lim : Ab_limit_d hZF ω.val cY.val Y.val F C.val U.val d X V J σ A Q T)
    (filter : Ab_filter_d F C.val U.val H₀) :
    ∃ H, Gset_d Q T Q X H ∧ ∀ p, M.mem p H ↔ M.mem p Q ∧ ∃ z, Rd_entry_d p z σ ∧ M.mem z H₀ := by
  let L := smdl_structure_l I (R := V) lim.model.1.2.1
  have hL := ZFC.models_zf_l (lim.theory.native_l I hZF lim.omega)
  let q : L.Domain := ⟨Q,lim.inside.2.2.1⟩
  let t : L.Domain := ⟨T,lim.inside.2.2.2⟩
  have li : Function.Injective (Subtype.val : L.Domain → M.Domain) := fun _ _ eq => Subtype.ext eq
  have lf := smem_full_l I lim.model lim.transitive
  have lmem {a b : L.Domain} : M.mem a.val b.val ↔ L.mem a b := image_member_l (M := L) (N := M) Subtype.val li lf
  have lent := image_entry_iff_l (M := L) (N := M) Subtype.val li lf (KP.exists_pair (ZF.modelsKP hL)) hZF.1
  have order := lim.product.order_l hL
  -- 每个原生成元都有同一极限腿给出的真实原像。
  have pull z (gen : Ab_gen_d F z) : ∃ p, M.mem p X ∧ M.mem p Q ∧ Rd_entry_d p z σ := by
    obtain ⟨i,r,v,a,ir,vr,ha,az⟩ := gen.read_l
    obtain ⟨j,ij⟩ := (lim.domain i).mp (run.function.bound_l ir).1
    obtain ⟨leg,square,_,_⟩ := lim.rows i r _ j ir vr ij
    obtain ⟨p,ap,pz⟩ := (square.2 a z).mp az
    have pc := run.returned_condition_l hZF lim.omega ctx ir vr ha az
    exact ⟨p,leg.1.1.output_mem_of_pairMember ap,
      (lim.returns.member_l I hZF lim.omega lim.model run.target pz lim.product_image).mpr pc,pz⟩
  let ρ : Env M 2 := ⟨fun k => [σ,H₀].get k,fun _ => σ⟩
  let φ : UnarySchema 2 := { body := .existsE (.conj (rd_entry0_m (.bound 1) .newest (.bound 2)) (.mem .newest (.bound 3))) }
  have read p : φ.denote ρ p ↔ ∃ z, Rd_entry_d p z σ ∧ M.mem z H₀ := by
    simp only [φ,UnarySchema.denote,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,rd_entry0_sat_l hZF.1,Formula.satisfies_mem_iff]
    rfl
  obtain ⟨H,sep⟩ := ZF.separation_exists_d hZF φ ρ Q
  have members p := (sep p).trans (and_congr_right fun _ => read p)
  have sub : M.MemberSubset H Q := fun p hp => ((members p).mp hp).1
  have proper (p : L.Domain) (hp : M.mem p.val H) : L.mem p q ∧ p ≠ q := by
    refine ⟨lmem.mp (sub p.val hp),fun eq => ?_⟩
    have ep : p.val = Q := congrArg Subtype.val eq
    exact KP.mem_irrefl_d (ZF.modelsKP hZF) Q (ep ▸ sub p.val hp)
  have inhabited : ∃ p : L.Domain, M.mem p.val H := by
    obtain ⟨z,gen,hz⟩ := filter.inhabited
    obtain ⟨p,hp,pQ,pz⟩ := pull z gen
    exact ⟨⟨p,hp⟩,(members p).mpr ⟨pQ,z,pz,hz⟩⟩
  have upward (p r : L.Domain) (hp : M.mem p.val H) (hr : L.mem r q) (pr : Entry_d L p r t) : M.mem r.val H := by
    obtain ⟨_,z,pz,hz⟩ := (members p.val).mp hp
    obtain ⟨w,_,rw⟩ := lim.returns.1.1.2.2 r.val r.property
    have wC := (lim.returns.member_l I hZF lim.omega lim.model run.target rw lim.product_image).mp (lmem.mpr hr)
    have zw := (lim.returns.entry_l hZF lim.omega lim.transitive run.transitive lim.model run.target pz rw lim.order_image).mp ((lent p r t).mp pr)
    exact (members r.val).mpr ⟨lmem.mpr hr,w,rw,filter.upward z w hz wC zw⟩
  have directed (p r : L.Domain) (hp : M.mem p.val H) (hr : M.mem r.val H) :
      ∃ s : L.Domain, M.mem s.val H ∧ Entry_d L s p t ∧ Entry_d L s r t := by
    obtain ⟨_,z,pz,hz⟩ := (members p.val).mp hp
    obtain ⟨_,w,rw,hw₀⟩ := (members r.val).mp hr
    obtain ⟨a,gen,ha,az,aw⟩ := filter.directed z w hz hw₀
    obtain ⟨s,hs,sQ,sa⟩ := pull a gen
    let s₀ : L.Domain := ⟨s,hs⟩
    exact ⟨s₀,(members s).mpr ⟨sQ,a,sa,ha⟩,
      (lent s₀ p t).mpr ((lim.returns.entry_l hZF lim.omega lim.transitive run.transitive lim.model run.target sa pz lim.order_image).mpr az),
      (lent s₀ r t).mpr ((lim.returns.entry_l hZF lim.omega lim.transitive run.transitive lim.model run.target sa rw lim.order_image).mpr aw)⟩
  -- 极限的任意全局稠密参数先回收到真实出生行，再反射其全乘积稠密性。
  have hits (D : L.Domain) (dense : Dense_set_d L q t q D) : ∃ p : L.Domain, M.mem p.val H ∧ L.mem p D := by
    obtain ⟨i,j,x,ij,xD⟩ := lim.cover D.val D.property
    obtain ⟨r,_,ir⟩ := run.function.2.1 i ((lim.domain i).mpr ⟨j,ij⟩)
    obtain ⟨v,vr,_⟩ := run.columns_l hZF.1 model trans ir
    have data := (run.queues _ _ _ ir vr).frame
    obtain ⟨leg,square,pP,uU⟩ := lim.rows i r _ j ir vr ij
    let B := smdl_structure_l I (R := (v 2)) data.model.1.2.1
    have hB := ZFC.models_zf_l (data.theory.native_l I hZF lim.omega)
    let p₀ : B.Domain := ⟨(v 5),data.inside.2.2.1⟩
    let u₀ : B.Domain := ⟨(v 6),data.inside.2.2.2.1⟩
    let D₀ : B.Domain := ⟨x,leg.1.1.input_mem_of_pairMember xD⟩
    obtain ⟨e,elem,values⟩ := leg.project_l I hZF lim.omega data.model.1 lim.model.1
    have ep : e p₀ = q := Subtype.ext (leg.1.1.1.2 _ _ _ (values p₀) pP)
    have eu : e u₀ = t := Subtype.ext (leg.1.1.1.2 _ _ _ (values u₀) uU)
    have eD : e D₀ = D := Subtype.ext (leg.1.1.1.2 _ _ _ (values D₀) xD)
    let η : Env B 3 := ⟨fun k => [p₀,u₀,D₀].get k,fun _ => D₀⟩
    let ψ : Formula 1 3 := dense_set_m (.bound 0) (.bound 1) (.bound 0) (.bound 2)
    have transfer := elem ψ (by simp -implicitDefEqProofs [ψ,dense_set_m_freeClosed]) η
    have dense' : Dense_set_d L (e p₀) (e u₀) (e p₀) (e D₀) := by
      rw [ep,eu,eD]
      exact dense
    have dense₀ : Dense_set_d B p₀ u₀ p₀ D₀ := (dense_set_sat_l B hB.1 η _ _ _ _).mp
      (transfer.mpr ((dense_set_sat_l L hL.1 (image_env_l e η) _ _ _ _).mpr dense'))
    have denseM := (data.model.dense_code_l I hZF.1 data.transitive (ZF.modelsKP hB) p₀ u₀ p₀ D₀).mpr dense₀
    obtain ⟨k,s,w,E,_,ks,ws,xE,DE,_,hit,accepted⟩ := run.dense_hit_l hZF model trans lim.omega
      ir vr D₀.property denseM
    have imageD : Rd_entry_d D.val E σ := by
      obtain ⟨y,xy,yE⟩ := (square.2 x E).mp xE
      exact leg.1.1.1.2 _ _ _ xy xD ▸ yE
    have state := run.queues k s w ks ws
    obtain ⟨z,_,az⟩ := state.frame.returns.1.1.2.2 (w 21) state.task.condition_inside
    have zE := (state.frame.returns.member_l I hZF lim.omega state.frame.model run.target az DE).mp hit
    have gen : Ab_gen_d F z := ⟨k,s,w 11,w 3,w 21,ks,⟨w,ws,rfl⟩,⟨w,ws,rfl⟩,accepted,az⟩
    have zC := run.returned_condition_l hZF lim.omega ctx ks ws accepted az
    have zH := (filter.members z).mpr ⟨zC,z,gen,ctx.order.refl z zC⟩
    obtain ⟨p,hp,pQ,pz⟩ := pull z gen
    let p' : L.Domain := ⟨p,hp⟩
    exact ⟨p',(members p).mpr ⟨pQ,z,pz,zH⟩,lmem.mp
      ((lim.returns.member_l I hZF lim.omega lim.model run.target pz imageD).mpr zE)⟩
  have generic : Generic_d L q t q (fun p => M.mem p.val H) := by
    refine ⟨proper,inhabited,upward,directed,?_⟩
    intro p hp D dense
    obtain ⟨E,global,description⟩ := dense_globalize_l hL order (proper p hp).1 dense
    obtain ⟨a,ha,aE⟩ := hits E global
    rcases ((description a).mp aE).2.2 with no | hit
    · obtain ⟨s,hs,sa,sp⟩ := directed a p ha hp
      exact (no ⟨s,⟨(proper s hs).1,(proper s hs).2,sa⟩,sp⟩).elim
    · exact ⟨a,ha,hit.2⟩
  exact ⟨H,(lim.model.generic_code_l I hZF.1 lim.transitive (ZF.modelsKP hL) q t q H).mpr ⟨sub,generic⟩,members⟩

/-- 同一原运行生产全乘积泛型、壳内实数种子及实际扩张的严格高度界。 -/
theorem Ab_run_d.generic_l {ω cY Y S : (smdl_structure_l I (R := R) model.1.2.1).Domain}
    {F T₀ Q₀ G₀ U₀ : M.Domain}
    (hΩ : M.IsOmega ω.val)
    (run : Ab_run_d I P ω.val cY.val Y.val S.val F)
    (system : Wi_state_d (kp_pair_l (ZF.modelsKP hZF)) ω.val ω.val T₀ Q₀ G₀ cY.val Y.val S.val U₀)
    (records : ∀ i r (v : Fin 26 → M.Domain), Rd_entry_d i r F → Rt_tuple_d v r → Wi_keep_d (v 23) (v 24) (v 25) Q₀ G₀ U₀) :
    Ab_generic_d hZF P ω.val cY.val Y.val F := by
  obtain ⟨C,U,ctx⟩ := run.return_order_l hZF model trans hΩ
  obtain ⟨H₀,filter⟩ := run.filter_l hZF model trans hΩ ctx
  obtain ⟨d,X,V,J,σ,A,Q,T,lim⟩ := run.limit_l hZF model trans hΩ ctx system records
  obtain ⟨H,generic,values⟩ := lim.generic_l hZF model trans run ctx filter
  obtain ⟨B,Z,hB,hZ,space,seed⟩ := run.seed
  obtain ⟨θ,hθ,bound⟩ := run.height
  exact ⟨C.val,U.val,H₀,d,X,V,J,σ,A,Q,T,H,ctx,filter,lim,generic,values,B,Z,θ,trans Y.val Y.property B hB,trans Y.val Y.property Z hZ,hB,hZ,space,seed,hθ,bound,
    lim.height_l hZF run.target run.transitive bound,
    lim.extension_height_l hZF run.target run.transitive bound generic⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 同一极限泛型接受旧条件，旧短前缀滤子留在测试模型

接受关系直接读原返回生成族。短前缀的背景集合在 P 内分离，再与外层
规范投影按成员方程识别；因此其泛型性与属于 P 是同一个对象的性质。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 极限接受原条件只依赖背景帧及同一返回生成滤子。 -/
theorem Ab_limit_d.condition_l {P ω cY Y S C U F d X V J σ A Q T H H₀ i r j q q' : M.Domain}
    {v : Fin 26 → M.Domain}
    (run : Ab_run_d I P ω cY Y S F) (ctx : Ab_return_order_d F C U)
    (filter : Ab_filter_d F C U H₀)
    (lim : Ab_limit_d hZF ω cY Y F C U d X V J σ A Q T)
    (members : ∀ p, M.mem p H ↔ M.mem p Q ∧ ∃ z, Rd_entry_d p z σ ∧ M.mem z H₀)
    (ir : Rd_entry_d i r F) (vr : Rt_tuple_d v r) (ij : Rd_entry_d i j J)
    (hq : M.mem q (v 11)) (image : Rd_entry_d q q' j) : M.mem q' H := by
  have frame := (run.queues i r v ir vr).frame
  have hp := (frame.filter_data_l hZF lim.omega).1 q hq
  obtain ⟨leg,square,pQ,_⟩ := lim.rows i r v j ir vr ij
  have qQ := (leg.member_l I hZF lim.omega frame.model lim.model image pQ).mp hp
  obtain ⟨z,_,qz⟩ := lim.returns.1.1.2.2 q' (leg.1.1.output_mem_of_pairMember image)
  have old := (square.2 q z).mpr ⟨q',image,qz⟩
  have zC := (lim.returns.member_l I hZF lim.omega lim.model run.target qz lim.product_image).mp qQ
  have gen : Ab_gen_d F z := ⟨i,r,v 11,v 3,q,ir,⟨v,vr,rfl⟩,⟨v,vr,rfl⟩,hq,old⟩
  exact (members q').mpr ⟨qQ,z,qz,(filter.members z).mpr ⟨zC,z,gen,ctx.order.refl z zC⟩⟩

variable {c P R : M.Domain}
  (model : Smem_d (kp_pair_l (ZF.modelsKP hZF)) c P R) (trans : M.TransitiveSet P)
include trans

theorem Ab_run_d.prefix_filter_l {ω cY Y S : (smdl_structure_l I (R := R) model.1.2.1).Domain}
    {F : M.Domain} {v : Fin 26 → (smdl_structure_l I (R := R) model.1.2.1).Domain}
    (hΩ : M.IsOmega ω.val)
    (run : Ab_run_d I P ω.val cY.val Y.val S.val F)
    (data : Ab_frame_d I ω.val cY.val Y.val (ab_head_v (fun k => (v k).val)))
    {n B T : (smdl_structure_l I (R := (v 2).val) data.model.1.2.1).Domain}
    (hn : (smdl_structure_l I (R := (v 2).val) data.model.1.2.1).mem n ⟨ω.val,data.inside.1⟩)
    (sub : M.MemberSubset n.val (v 7).val)
    (stage : Fp_prefix_d (ZFC.models_zf_l (data.theory.native_l I hZF hΩ))
      ⟨ω.val,data.inside.1⟩ ⟨(v 4).val,data.inside.2.1⟩ n B T) :
    ∃ K, M.mem K P ∧ Fp_filter_project_d B.val (v 6).val (v 11).val K ∧
      Gset_d B.val T.val B.val (v 1).val K := by
  let L := smdl_structure_l I (R := (v 2).val) data.model.1.2.1
  have hL := ZFC.models_zf_l (data.theory.native_l I hZF hΩ)
  let w : L.Domain := ⟨ω.val,data.inside.1⟩
  let a : L.Domain := ⟨(v 4).val,data.inside.2.1⟩
  let p : L.Domain := ⟨(v 5).val,data.inside.2.2.1⟩
  let t : L.Domain := ⟨(v 6).val,data.inside.2.2.2.1⟩
  let m : L.Domain := ⟨(v 7).val,data.inside.2.2.2.2.1⟩
  let b : L.Domain := ⟨(v 8).val,data.inside.2.2.2.2.2.1⟩
  let s : L.Domain := ⟨(v 9).val,data.inside.2.2.2.2.2.2.1⟩
  obtain ⟨_,_,product,large⟩ := (ab_kernel_read_l I data.model data.transitive hL w a p t m b s).mp data.kernel
  have hm : L.mem m w := (data.model.2 m.val w.val).mpr ⟨m.property,w.property,
    data.index⟩
  have sub' : L.MemberSubset n m := fun x hx => (data.model.2 x.val m.val).mpr
    ⟨x.property,m.property,sub x.val ((data.model.2 x.val n.val).mp hx).2.2⟩
  obtain ⟨K,proj,gK⟩ := Model.Forcing.Internal.Smem_d.prefix_project_l hZF data.model data.transitive hL
    hn hm sub' product stage large data.generic
  obtain ⟨K₀,hK₀,proj₀⟩ := run.projects B.val (v 6).val (v 11).val
    (trans (v 1).val (v 1).property B.val B.property) (v 6).property (v 11).property
  exact ⟨K₀,hK₀,proj₀,proj.unique_l hZF.1 proj₀ ▸ gK⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 极限全乘积的实际前缀泛型及旧实数名字提升

派生实数只取有限前缀扩张的实数并集。旧名字沿原极限腿提升，原生成元的
返回像保证条件被同一全乘积泛型接受；逐点固定 ω 保证解释仍是原完整实数图。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Ab_limit_real_d {ω cY Y F C U d X V J σ A Q T : M.Domain}
    (lim : Ab_limit_d hZF ω cY Y F C U d X V J σ A Q T) (H x : M.Domain) : Prop :=
  let hL := ZFC.models_zf_l (lim.theory.native_l I hZF lim.omega)
  Rp_bg_d hZF lim.model hL ⟨ω,lim.inside.1⟩ ⟨A,lim.inside.2.1⟩ ⟨T,lim.inside.2.2.2⟩ H x

/-- 量化每个真实前缀扩张的全部实数，并输出其属于指定实数集的完整图。 -/
def Ab_prefix_reals_d {ω cY Y F C U d X V J σ A Q T : M.Domain}
    (lim : Ab_limit_d hZF ω cY Y F C U d X V J σ A Q T) (H B : M.Domain) : Prop :=
  let L := smdl_structure_l I (R := V) lim.model.1.2.1
  let hL := ZFC.models_zf_l (lim.theory.native_l I hZF lim.omega)
  let w : L.Domain := ⟨ω,lim.inside.1⟩
  ∀ n : L.Domain, L.mem n w → ∃ C S : L.Domain, ∃ K : M.Domain,
    Fp_prefix_d hL w ⟨A,lim.inside.2.1⟩ n C S ∧ Fp_filter_project_d C.val T H K ∧ Gset_d C.val S.val C.val X K ∧
    let G : L.Domain → Prop := fun p => M.mem p.val K
    let E := extension_l L hL C S C G
    ∃ j : L.Domain → E.Domain, (∀ a, Gval_d L C S C G a (j a)) ∧
      ∀ y, Fn0_d (j w) (j w) y → ∃ x, M.mem x B ∧ Fn_read_d Subtype.val j y x

theorem Ab_limit_d.prefix_generic_l {ω cY Y F C U d X V J σ A Q T H : M.Domain}
    (lim : Ab_limit_d hZF ω cY Y F C U d X V J σ A Q T) (generic : Gset_d Q T Q X H)
    {n B S : (smdl_structure_l I (R := V) lim.model.1.2.1).Domain}
    (hn : (smdl_structure_l I (R := V) lim.model.1.2.1).mem n ⟨ω,lim.inside.1⟩)
    (stage : Fp_prefix_d (ZFC.models_zf_l (lim.theory.native_l I hZF lim.omega))
      ⟨ω,lim.inside.1⟩ ⟨A,lim.inside.2.1⟩ n B S) :
    ∃ K, Fp_filter_project_d B.val T H K ∧ Gset_d B.val S.val B.val X K := by
  let L := smdl_structure_l I (R := V) lim.model.1.2.1
  have hL := ZFC.models_zf_l (lim.theory.native_l I hZF lim.omega)
  obtain ⟨W,range⟩ := ZF.exists_range_of_setFunction hL (kp_pair_l (ZF.modelsKP hL))
    lim.alphabet.function lim.alphabet.domain
  have fa : L.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hL)) ⟨A,lim.inside.2.1⟩ ⟨ω,lim.inside.1⟩ W :=
    ⟨lim.alphabet.function,lim.alphabet.domain,by
    intro i hi
    obtain ⟨a,ia⟩ := (lim.alphabet.domain i).mp hi
    exact ⟨a,(range a).mpr ⟨i,ia⟩,ia⟩⟩
  exact Model.Forcing.Internal.Smem_d.product_project_l hZF lim.model lim.transitive hL
    lim.clock hn fa lim.product stage generic

theorem Ab_limit_d.prefix_values_l {ω cY Y F C U d X V J σ A Q T H B : M.Domain}
    (lim : Ab_limit_d hZF ω cY Y F C U d X V J σ A Q T) (generic : Gset_d Q T Q X H)
    (inside : ∀ x, Ab_limit_real_d hZF lim H x → M.mem x B) : Ab_prefix_reals_d hZF lim H B := by
  let L := smdl_structure_l I (R := V) lim.model.1.2.1
  have hL := ZFC.models_zf_l (lim.theory.native_l I hZF lim.omega)
  intro n hn
  obtain ⟨C,S,stage⟩ := lim.product.prefix_l hL hn
  obtain ⟨K,projection,gK⟩ := lim.prefix_generic_l hZF generic hn stage
  obtain ⟨j,ground,all⟩ := real_values_background_l hZF lim.model lim.transitive hL
    (ω := (⟨ω,lim.inside.1⟩ : L.Domain)) (stage.order_l hL) gK
  refine ⟨C,S,K,stage,projection,gK,j,ground,fun y hy => ?_⟩
  obtain ⟨x,real,code,read⟩ := all y hy
  exact ⟨x,inside x ⟨real,n,C,S,⟨ω,lim.inside.1⟩,K,hn,stage,projection,code⟩,read⟩

theorem Ab_limit_d.stage_real_l {P ω cY Y S C U F d X V J σ A Q T H H₀ x : M.Domain}
    (run : Ab_run_d I P ω cY Y S F) (ctx : Ab_return_order_d F C U)
    (filter : Ab_filter_d F C U H₀)
    (lim : Ab_limit_d hZF ω cY Y F C U d X V J σ A Q T)
    (generic : Gset_d Q T Q X H)
    (members : ∀ p, M.mem p H ↔ M.mem p Q ∧ ∃ z, Rd_entry_d p z σ ∧ M.mem z H₀)
    (real : Ab_stage_real_d ω F x) : Ab_limit_real_d hZF lim H x := by
  let L := smdl_structure_l I (R := V) lim.model.1.2.1
  have hL := ZFC.models_zf_l (lim.theory.native_l I hZF lim.omega)
  obtain ⟨fx,i,r,v,E,ir,vr,hE,code⟩ := real
  have data := (run.queues i r v ir vr).frame
  let B := smdl_structure_l I (R := (v 2)) data.model.1.2.1
  have hB := ZFC.models_zf_l (data.theory.native_l I hZF lim.omega)
  let ω₀ : B.Domain := ⟨ω,data.inside.1⟩
  let a : B.Domain := ⟨(v 4),data.inside.2.1⟩
  let p : B.Domain := ⟨(v 5),data.inside.2.2.1⟩
  let t : B.Domain := ⟨(v 6),data.inside.2.2.2.1⟩
  let n : B.Domain := ⟨(v 7),data.inside.2.2.2.2.1⟩
  let b : B.Domain := ⟨(v 8),data.inside.2.2.2.2.2.1⟩
  let s : B.Domain := ⟨(v 9),data.inside.2.2.2.2.2.2.1⟩
  let E₀ : B.Domain := ⟨E,hE⟩
  obtain ⟨_,_,product,stage⟩ := (ab_kernel_read_l I data.model data.transitive hB ω₀ a p t n b s).mp data.kernel
  obtain ⟨j,ij⟩ := (lim.domain i).mp (run.function.bound_l ir).1
  obtain ⟨leg,_,pQ,tT⟩ := lim.rows i r _ j ir vr ij
  obtain ⟨e,elem,values⟩ := leg.project_l I hZF lim.omega data.model.1 lim.model.1
  have ew : e ω₀ = (⟨ω,lim.inside.1⟩ : L.Domain) := Subtype.ext
    (leg.1.1.1.2 _ _ _ (values ω₀) (leg.omega_l I hZF lim.omega data.transitive lim.transitive data.model lim.model data.inside.1))
  have ep : e p = (⟨Q,lim.inside.2.2.1⟩ : L.Domain) := Subtype.ext (leg.1.1.1.2 _ _ _ (values p) pQ)
  have et : e t = (⟨T,lim.inside.2.2.2⟩ : L.Domain) := Subtype.ext (leg.1.1.1.2 _ _ _ (values t) tT)
  have li : Function.Injective (Subtype.val : L.Domain → M.Domain) := fun _ _ eq => Subtype.ext eq
  have lf := smem_full_l I lim.model lim.transitive
  have le := image_entry_iff_l (M := L) (N := M) Subtype.val li lf (KP.exists_pair (ZF.modelsKP hL)) hZF.1
  have nm : B.mem n ω₀ := (data.model.2 n.val ω).mpr ⟨n.property,ω₀.property,
    data.index⟩
  have hn : L.mem (e n) ⟨ω,lim.inside.1⟩ := ew ▸ (em_member_l e elem n ω₀).mp nm
  have product' := fp_product_image_l hB hL e elem product
  have stage' := fp_prefix_image_l hB hL e elem stage
  rw [ew,ep,et] at product'
  rw [ew] at stage'
  have canonical := stage'.rebase_l hL product' lim.product hn
  obtain ⟨K,projection,gK⟩ := lim.prefix_generic_l hZF generic hn canonical
  have accepted (q : B.Domain) (hq : M.mem q.val (v 11)) : M.mem (e q).val K := by
    have qb : B.mem q b := (data.model.2 q.val b.val).mpr ⟨q.property,b.property,(data.generic.proper q.val hq).1⟩
    have qH := lim.condition_l hZF run ctx filter members ir vr ij hq (values q)
    have qQ := (generic.proper (e q).val qH).1
    exact (projection (e q).val).mpr ⟨(image_member_l (M := L) (N := M) Subtype.val li lf).mpr
      ((em_member_l e elem q b).mp qb),(e q).val,qH,(le (e q) (e q) ⟨T,lim.inside.2.2.2⟩).mp
        ((lim.product.order_l hL).refl (e q) ((image_member_l (M := L) (N := M) Subtype.val li lf).mp qQ))⟩
  have g := ((lim.model.generic_code_l I hZF.1 lim.transitive (ZF.modelsKP hL) (e b) (e s) (e b) K).mp gK).2
  have fixed (q : B.Domain) (hq : B.mem q ω₀) : (e q).val = q.val := leg.1.1.1.2 _ _ _ (values q)
    (leg.natural_l hZF lim.omega data.transitive lim.transitive data.model lim.model data.inside.1 q.val
      ((data.model.2 q.val ω).mp hq).2.2)
  have lifted := fn_code_real_lift_l (ZF.modelsKP hZF) hB.1 hL e elem Subtype.val
    (fun _ _ eq => Subtype.ext eq) (smem_full_l I data.model data.transitive) Subtype.val li lf
    (congrArg Subtype.val ew) fixed (em_order_l hB.1 hL.1 e elem (stage.order_l hB)) g accepted fx
    ((fn_bg_read_l I hZF.1 data.model data.transitive hB.1 b s b ω₀ E₀ (v 11) x).mp code)
  have named := (fn_bg_read_l I hZF.1 lim.model lim.transitive hL.1 (e b) (e s) (e b) (e ω₀) (e E₀) K x).mpr lifted
  refine ⟨fx,e n,e b,e s,e E₀,K,hn,canonical,projection,?_⟩
  simpa only [ew] using named

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 极限有限前缀的全部实数回收到测试模型

将条件域、顺序和解释名字编码为一份有限记录，在足够晚的原阶段共同回收。
原前缀泛型在 P 内投影到所需长度。泛型提升的初等性反射名字的实数性质，
并逐边保留背景图；原有界图闭包恢复同一实数，无需测试壳满足 ZF。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF) {c P R : M.Domain}
  (model : Smem_d (kp_pair_l (ZF.modelsKP hZF)) c P R) (trans : M.TransitiveSet P)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
include trans

theorem Ab_limit_d.real_inside_l {ω cY Y S C U : (smdl_structure_l I (R := R) model.1.2.1).Domain}
    {F d X V J σ A Q T H H₀ x : M.Domain}
    (run : Ab_run_d I P ω.val cY.val Y.val S.val F) (ctx : Ab_return_order_d F C.val U.val)
    (filter : Ab_filter_d F C.val U.val H₀)
    (lim : Ab_limit_d hZF ω.val cY.val Y.val F C.val U.val d X V J σ A Q T)
    (generic : Gset_d Q T Q X H)
    (members : ∀ p, M.mem p H ↔ M.mem p Q ∧ ∃ z, Rd_entry_d p z σ ∧ M.mem z H₀)
    (real : Ab_limit_real_d hZF lim H x) : M.mem x P := by
  let N := smdl_structure_l I (R := R) model.1.2.1
  let L := smdl_structure_l I (R := V) lim.model.1.2.1
  have hL := ZFC.models_zf_l (lim.theory.native_l I hZF lim.omega)
  have li : Function.Injective (Subtype.val : L.Domain → M.Domain) := fun _ _ eq => Subtype.ext eq
  have lf := smem_full_l I lim.model lim.transitive
  obtain ⟨fx,n,B,S',E,K,hn,stage,projection,code⟩ := real
  obtain ⟨K',projection',gK'⟩ := lim.prefix_generic_l hZF generic hn stage
  have gK : Gset_d B.val S'.val B.val X K := (projection'.unique_l hZF.1 projection) ▸ gK'
  have g := ((lim.model.generic_code_l I hZF.1 lim.transitive (ZF.modelsKP hL) B S' B K).mp gK).2
  obtain ⟨τ,k,y,value,ground,fy,read⟩ :=
    ((fn_bg_read_l I hZF.1 lim.model lim.transitive hL.1 B S' B ⟨ω.val,lim.inside.1⟩ E K x).mp code).real_value_l
      (ZF.modelsKP hZF) hL Subtype.val li lf (stage.order_l hL) g fx
  -- 一份记录同时携带偏序参数和名字；内部任意长度 n 均可指定为回收下界。
  let w : Fin 3 → L.Domain := fun i => [B,S',τ].get i
  obtain ⟨z,tuple⟩ := rt_tuple_exists_l (ZF.modelsKP hL) w
  have hnM : M.mem n.val ω.val := (image_member_l (M := L) (N := M) Subtype.val li lf).mpr hn
  obtain ⟨i,j,z₀,above,ij,zz⟩ := lim.cover_after n.val hnM z.val z.property
  obtain ⟨r,_,ir⟩ := run.function.2.1 i ((lim.domain i).mpr ⟨j,ij⟩)
  obtain ⟨w,wr,_,_,successor⟩ := run.columns_l hZF.1 model trans ir
  have owned := Internal.Rt_tuple_d.members_l wr trans (run.function.bound_l ir).2
  let v (k : Fin 26) : N.Domain := ⟨w k,owned k⟩
  have vr : Rt_tuple_d (fun k => (v k).val) r := wr
  have data := (run.queues _ _ _ ir vr).frame
  obtain ⟨leg,_,pQ,tT⟩ := lim.rows i r _ j ir vr ij
  obtain ⟨v₀,_,images⟩ := leg.tuple_preimage_l hZF lim.omega data.transitive lim.transitive data.model lim.model
    zz (tuple.image_l Subtype.val lf)
  let D := smdl_structure_l I (R := (v 2).val) data.model.1.2.1
  have hD := ZFC.models_zf_l (data.theory.native_l I hZF lim.omega)
  let ω₀ : D.Domain := ⟨ω.val,data.inside.1⟩
  let a : D.Domain := ⟨(v 4).val,data.inside.2.1⟩
  let p : D.Domain := ⟨(v 5).val,data.inside.2.2.1⟩
  let t : D.Domain := ⟨(v 6).val,data.inside.2.2.2.1⟩
  let m : D.Domain := ⟨(v 7).val,data.inside.2.2.2.2.1⟩
  let b : D.Domain := ⟨v₀ 0,leg.1.1.input_mem_of_pairMember (images 0)⟩
  let s : D.Domain := ⟨v₀ 1,leg.1.1.input_mem_of_pairMember (images 1)⟩
  let τ₀ : D.Domain := ⟨v₀ 2,leg.1.1.input_mem_of_pairMember (images 2)⟩
  let n₀ : D.Domain := ⟨n.val,data.transitive ω.val ω₀.property n.val hnM⟩
  have di : Function.Injective (Subtype.val : D.Domain → M.Domain) := fun _ _ eq => Subtype.ext eq
  have df := smem_full_l I data.model data.transitive
  obtain ⟨e,elem,values⟩ := leg.project_l I hZF lim.omega data.model.1 lim.model.1
  have ew : e ω₀ = (⟨ω.val,lim.inside.1⟩ : L.Domain) := Subtype.ext (leg.1.1.1.2 _ _ _ (values ω₀)
    (leg.omega_l I hZF lim.omega data.transitive lim.transitive data.model lim.model data.inside.1))
  have eb : e b = B := Subtype.ext (leg.1.1.1.2 _ _ _ (values b) (images 0))
  have es : e s = S' := Subtype.ext (leg.1.1.1.2 _ _ _ (values s) (images 1))
  have eτ : e τ₀ = τ := Subtype.ext (leg.1.1.1.2 _ _ _ (values τ₀) (images 2))
  have en : e n₀ = n := Subtype.ext (leg.1.1.1.2 _ _ _ (values n₀)
    (leg.natural_l hZF lim.omega data.transitive lim.transitive data.model lim.model data.inside.1 n.val hnM))
  have ep : e p = (⟨Q,lim.inside.2.2.1⟩ : L.Domain) := Subtype.ext (leg.1.1.1.2 _ _ _ (values p) pQ)
  have et : e t = (⟨T,lim.inside.2.2.2⟩ : L.Domain) := Subtype.ext (leg.1.1.1.2 _ _ _ (values t) tT)
  obtain ⟨_,_,product,_⟩ := (ab_kernel_read_l I data.model data.transitive hD ω₀ a p t m
    ⟨(v 8).val,data.inside.2.2.2.2.2.1⟩ ⟨(v 9).val,data.inside.2.2.2.2.2.2.1⟩).mp data.kernel
  have movedProduct := fp_product_image_l hD hL e elem product
  rw [ew,ep,et] at movedProduct
  have movedStage : Fp_prefix_d hL (e ω₀) (e a) (e n₀) (e b) (e s) := by
    rw [ew,en,eb,es]
    exact stage.rebase_l hL lim.product movedProduct hn
  have oldStage : Fp_prefix_d hD ω₀ a n₀ b s := by
    let ρ : Env D 5 := ⟨fun i => [ω₀,a,n₀,b,s].get i,fun _ => b⟩
    let φ := fp_prefix_m (.bound 0 : Term 5) (.bound 1) (.bound 2) (.bound 3) (.bound 4)
    exact (fp_prefix_sat_l hD ρ _ _ _ _ _).mp ((elem φ (by simp -implicitDefEqProofs [φ]) ρ).mpr
      ((fp_prefix_sat_l hL (image_env_l e ρ) _ _ _ _ _).mpr movedStage))
  have hn₀ : D.mem n₀ ω₀ := (image_member_l (M := D) (N := M) Subtype.val di df).mp hnM
  have nm : M.mem n.val (v 7).val := above.elim (fun eq => eq.symm ▸ successor.predecessor_mem)
    (fun lt => (successor n.val).mpr (Or.inl lt))
  have hm : M.mem (v 7).val ω.val := data.index
  have sub := (lim.omega.members_areOrdinals (ZF.modelsKP hZF) (v 7).val hm).transitive n.val nm
  obtain ⟨K₀,hK₀,proj₀,g₀⟩ := run.prefix_filter_l hZF model trans lim.omega data hn₀ sub oldStage
  have oldGeneric := ((data.model.generic_code_l I hZF.1 data.transitive (ZF.modelsKP hD) b s b K₀).mp g₀).2
  have newGeneric : Generic_d L (e b) (e s) (e b) (fun q => M.mem q.val K) := by
    rw [eb,es]
    exact g
  -- 投影中的每个旧条件由原长前缀接受条件加强；同一极限泛型接受其像。
  have accepted (q : D.Domain) (hq : M.mem q.val K₀) : M.mem (e q).val K := by
    obtain ⟨qb,u,hu,uq⟩ := (proj₀ q.val).mp hq
    have gm := data.generic
    let u₀ : D.Domain := ⟨u,data.transitive (v 8).val data.inside.2.2.2.2.2.1 u (gm.proper u hu).1⟩
    have uH := lim.condition_l hZF run ctx filter members ir vr ij hu (values u₀)
    have qB : M.mem (e q).val B.val := congrArg Subtype.val eb ▸
      (image_member_l (M := L) (N := M) Subtype.val li lf).mpr
        ((em_member_l e elem q b).mp ((image_member_l (M := D) (N := M) Subtype.val di df).mp qb))
    have order := (leg.entry_l hZF lim.omega data.transitive lim.transitive data.model lim.model
      (values u₀) (values q) tT).mp uq
    exact (projection (e q).val).mpr ⟨qB,(e u₀).val,uH,order⟩
  have fixed (q : D.Domain) (hq : D.mem q ω₀) : (e q).val = q.val := leg.1.1.1.2 _ _ _ (values q)
    (leg.natural_l hZF lim.omega data.transitive lim.transitive data.model lim.model data.inside.1 q.val
      ((image_member_l (M := D) (N := M) Subtype.val di df).mpr hq))
  have oldCode : Fn_code_d (M := M) Subtype.val b s b ω₀ ω₀ (fun q => M.mem q.val K₀) x := by
    have pull := fn_value_real_pull_l (ZF.modelsKP hZF) hD hL e elem Subtype.val di df Subtype.val li fixed
      (oldStage.order_l hD) oldGeneric newGeneric accepted (τ := τ₀) (x := x)
    rw [eb,es,ew,eτ] at pull
    exact (pull k ground value fy read fx).code_l hD (oldStage.order_l hD) oldGeneric
  have named := (fn_bg_read_l I hZF.1 data.model data.transitive hD.1 b s b ω₀ ω₀ K₀ x).mpr oldCode
  let bP : N.Domain := ⟨b.val,trans (v 1).val (v 1).property b.val b.property⟩
  let sP : N.Domain := ⟨s.val,trans (v 1).val (v 1).property s.val s.property⟩
  exact Rg_closed_d.real_code_inside_l hZF run.graphs trans (v 1).property bP.property sP.property bP.property hK₀ named
    (fn0_function_l (ZF.modelsKP hZF) fx).1.1

/-- 同一全乘积泛型的有限前缀实数并集，恰为测试模型的全部实数。 -/
theorem Ab_limit_d.reals_l {ω cY Y S C U : (smdl_structure_l I (R := R) model.1.2.1).Domain}
    {F d X V J σ A Q T H H₀ B : M.Domain}
    (space : Rb_reals_d P ω.val B)
    (run : Ab_run_d I P ω.val cY.val Y.val S.val F) (ctx : Ab_return_order_d F C.val U.val)
    (filter : Ab_filter_d F C.val U.val H₀)
    (lim : Ab_limit_d hZF ω.val cY.val Y.val F C.val U.val d X V J σ A Q T)
    (generic : Gset_d Q T Q X H)
    (members : ∀ p, M.mem p H ↔ M.mem p Q ∧ ∃ z, Rd_entry_d p z σ ∧ M.mem z H₀) :
    ∀ x, Ab_limit_real_d hZF lim H x ↔ M.mem x B := by
  intro x
  constructor
  · intro real
    exact (space x).mpr ⟨lim.real_inside_l hZF model trans run ctx filter generic members real,real.1⟩
  · intro hx
    exact lim.stage_real_l hZF run ctx filter generic members
      ((run.stage_reals_l hZF model trans space x).mpr hx)

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原吸收极限中的规范实数并名字及尾部固定证书

使用已经构造的同一极限、字母表、全乘积和泛型。名字存在于该极限模型，
其解释恰为有限前缀实数并；任意实际尾部作用在所有条件上迫使原名字等值。
同一名字还携带尾部弱齐性、地参数的顶条件判定及固定前缀后的全部尾延伸真值判定。
商扩张中的每个成员与测试模型中的实数以完整函数图双向唯一对应。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Ab_real_name_d {ω cY Y F C U d X V J σ A Q T : M.Domain}
    (lim : Ab_limit_d hZF ω cY Y F C U d X V J σ A Q T) (H B : M.Domain) : Prop :=
  let L := smdl_structure_l I (R := V) lim.model.1.2.1
  let hL := ZFC.models_zf_l (lim.theory.native_l I hZF lim.omega)
  let w : L.Domain := ⟨ω,lim.inside.1⟩
  let a : L.Domain := ⟨A,lim.inside.2.1⟩
  let q : L.Domain := ⟨Q,lim.inside.2.2.1⟩
  let t : L.Domain := ⟨T,lim.inside.2.2.2⟩
  let G : L.Domain → Prop := fun p => M.mem p.val H
  let E := extension_l L hL q t q G
  ∃ r : L.Domain, Rp_name_d hL w a q r ∧
    (∀ n F s p, Fp_tail_d (kp_pair_l (ZF.modelsKP hL)) n q t F →
      Nmap_d L F r s → L.mem p q → Eq_force_d L q t q p s r) ∧
    Rp_decision_d hL w a q t r ∧
    ∃ Z : E.Domain, Qval_d L q t q G r Z ∧ (∀ y, E.mem y Z ↔ Rp_value_d hL w a q t G y) ∧
      ∃ j : L.Domain → E.Domain, (∀ s, Gval_d L q t q G s (j s)) ∧
        (∀ y, E.mem y Z → Fn0_d (j w) (j w) y ∧
          ∃ x, (M.mem x B ∧ Fn_read_d Subtype.val j y x) ∧
            ∀ z, (M.mem z B ∧ Fn_read_d Subtype.val j y z) → z = x) ∧
        ∀ x, M.mem x B → ∃ y, (E.mem y Z ∧ Fn_read_d Subtype.val j y x) ∧
          ∀ z, (E.mem z Z ∧ Fn_read_d Subtype.val j z x) → z = y

theorem Ab_limit_d.real_name_l {ω cY Y F C U d X V J σ A Q T H B : M.Domain}
    (lim : Ab_limit_d hZF ω cY Y F C U d X V J σ A Q T)
    (generic : Gset_d Q T Q X H) (same : ∀ x, Ab_limit_real_d hZF lim H x ↔ M.mem x B) :
    Ab_real_name_d hZF lim H B := by
  let L := smdl_structure_l I (R := V) lim.model.1.2.1
  have hL := ZFC.models_zf_l (lim.theory.native_l I hZF lim.omega)
  let w : L.Domain := ⟨ω,lim.inside.1⟩
  let a : L.Domain := ⟨A,lim.inside.2.1⟩
  let q : L.Domain := ⟨Q,lim.inside.2.2.1⟩
  let t : L.Domain := ⟨T,lim.inside.2.2.2⟩
  obtain ⟨W,range⟩ := ZF.exists_range_of_setFunction hL (kp_pair_l (ZF.modelsKP hL))
    lim.alphabet.function lim.alphabet.domain
  have fa : L.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hL)) a w W :=
    ⟨lim.alphabet.function,lim.alphabet.domain,fun i hi => by
      obtain ⟨b,ib⟩ := (lim.alphabet.domain i).mp hi
      exact ⟨b,(range b).mpr ⟨i,ib⟩,ib⟩⟩
  have g := ((lim.model.generic_code_l I hZF.1 lim.transitive (ZF.modelsKP hL) q t q H).mp generic).2
  obtain ⟨r,name⟩ := rp_name_exists_l hL lim.clock fa lim.product
  obtain ⟨Z,value,members⟩ := name.value_l hL lim.clock fa lim.product g
  obtain ⟨j,ground,forward,backward⟩ :=
    rp_background_l hZF lim.model lim.transitive hL lim.clock fa lim.product generic
  refine ⟨r,name,fun _ _ _ _ tail image hp => name.tail_eq_l hL lim.product tail image hp,
    name.decision_l hL lim.clock lim.alphabet.function lim.product,Z,value,members,j,ground,?_,?_⟩
  · intro y hy
    obtain ⟨fy,x,⟨real,read⟩,unique⟩ := forward y ((members y).mp hy)
    exact ⟨fy,x,⟨(same x).mp real,read⟩,fun z hz => unique z ⟨(same z).mpr hz.1,hz.2⟩⟩
  · intro x hx
    obtain ⟨y,⟨real,read⟩,unique⟩ := backward x ((same x).mpr hx)
    exact ⟨y,⟨(members y).mpr real,read⟩,fun z hz => unique z ⟨(members z).mp hz.1,hz.2⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 实际吸收扩张的派生 Jensen 层识别

原名字商的背景坍塌固定地参数，完整实数图对应识别规范名字值的像。
传递种子随之识别；每个扩张序数由原高度证书给出共同模型中的同一序数，
两侧实际 Σ₁ 递归证书的唯一性识别整层。共同层给出原派生模型到共同模型
L(ℝ) 的成员满映射，保留实数基集并运输原 8.3 的完整见证真值。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF) {c K R : M.Domain}
  (model : Smem_d (kp_pair_l (ZF.modelsKP hZF)) c K R)
  (native : (smdl_structure_l (kp_pair_l (ZF.modelsKP hZF)) (R := R) model.1.2.1).Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Ab_jensen_d (ω B : (smdl_structure_l I (R := R) model.1.2.1).Domain) (θ : M.Domain)
    {cY Y F C U d X V J σ A Q T : M.Domain}
    (lim : Ab_limit_d hZF ω.val cY Y F C U d X V J σ A Q T) (H : M.Domain) : Prop :=
  let L := smdl_structure_l I (R := V) lim.model.1.2.1
  let hL := ZFC.models_zf_l (lim.theory.native_l I hZF lim.omega)
  let q : L.Domain := ⟨Q,lim.inside.2.2.1⟩
  let t : L.Domain := ⟨T,lim.inside.2.2.2⟩
  let G : L.Domain → Prop := fun p => M.mem p.val H
  let E := extension_l L hL q t q G
  let N := smdl_structure_l I (R := R) model.1.2.1
  ∃ r : L.Domain, ∃ Z S : E.Domain, ∃ S₀ : N.Domain,
    Rp_name_d hL ⟨ω.val,lim.inside.1⟩ ⟨A,lim.inside.2.1⟩ q r ∧ Qval_d L q t q G r Z ∧
    Tc_d Z S ∧ Relative.Lr_seed_d native ω B S₀ ∧
    ∃ e : E.Domain → M.Domain, Function.Injective e ∧
      (∀ x y, M.mem y (e x) ↔ ∃ z, E.mem z x ∧ e z = y) ∧
      (∀ a x, Gval_d L q t q G a x → e x = a.val) ∧ e Z = B.val ∧ e S = S₀.val ∧
      (∀ ξ, E.IsOrdinal ξ → ∃ α : N.Domain, ∃ W : E.Domain, ∃ W₀ : N.Domain,
        N.IsOrdinal α ∧ M.mem α.val θ ∧ e ξ = α.val ∧
        Relative.Ja_d S ξ W ∧ Relative.Ja_d S₀ α W₀ ∧ e W = W₀.val) ∧
      ∃ hE : E.Models KPi, Relative.La_transport_d I model native hE S Z B e

theorem Ab_limit_d.jensen_l (trans : M.TransitiveSet K)
    {ω B : (smdl_structure_l I (R := R) model.1.2.1).Domain}
    {cY Y F C U d X V J σ A Q T H θ : M.Domain}
    (inside : M.MemberSubset Y K)
    (space : Baire_d (kp_pair_l (ZF.modelsKP native)) ω B)
    (lim : Ab_limit_d hZF ω.val cY Y F C U d X V J σ A Q T)
    (generic : Gset_d Q T Q X H) (names : Ab_real_name_d hZF lim H B.val)
    (height : Ab_extension_height_d hZF lim H θ) : Ab_jensen_d hZF model native ω B θ lim H := by
  let L := smdl_structure_l I (R := V) lim.model.1.2.1
  have hL := ZFC.models_zf_l (lim.theory.native_l I hZF lim.omega)
  let w : L.Domain := ⟨ω.val,lim.inside.1⟩
  let q : L.Domain := ⟨Q,lim.inside.2.2.1⟩
  let t : L.Domain := ⟨T,lim.inside.2.2.2⟩
  let G : L.Domain → Prop := fun p => M.mem p.val H
  let E := extension_l L hL q t q G
  let N := smdl_structure_l I (R := R) model.1.2.1
  have O := lim.product.order_l hL
  have g := ((lim.model.generic_code_l I hZF.1 lim.transitive (ZF.modelsKP hL) q t q H).mp generic).2
  have hE := preserves_zf_l O hL g
  obtain ⟨r,name,_,_,Z,value,_,j,ground,forward,backward⟩ := names
  obtain ⟨_,e,_,_,ei,ef,fixed⟩ := bg_extension_l hZF lim.model lim.transitive hL O generic
  have commute a : e (j a) = a.val := fixed a (j a) (ground a)
  have lf := smem_full_l I lim.model lim.transitive
  have ni : Function.Injective (Subtype.val : N.Domain → M.Domain) := fun _ _ eq => Subtype.ext eq
  have nf := smem_full_l I model trans
  have testReal {x : M.Domain} (hx : M.mem x B.val) : Fn0_d ω.val ω.val x := by
    obtain ⟨a,ha,rfl⟩ := (nf B x).mp hx
    exact fn0_of_function_l (ZF.modelsKP hZF) (image_function_l (M := N) (N := M) Subtype.val ni nf ((space.2 a).mp ha))
  -- 同一完整函数图的读取，在实际背景坍塌下成为对象相等。
  have realEq {y : E.Domain} {x : M.Domain} (fy : Fn0_d (j w) (j w) y)
      (fx : Fn0_d ω.val ω.val x) (read : Fn_read_d Subtype.val j y x) : e y = x := by
    exact read.image_eq_l (ZF.modelsKP hZF) (ZF.modelsKP hE) e ei ef lf commute fy
      (fn0_function_l (ZF.modelsKP hZF) fx).1.1
  have realSet : e Z = B.val := by
    apply hZF.1.eq_of_same_members
    intro x
    constructor
    · intro hx
      obtain ⟨y,hy,ey⟩ := (ef Z x).mp hx
      obtain ⟨fy,z,⟨hz,read⟩,_⟩ := forward y hy
      exact ((realEq fy (testReal hz) read).symm.trans ey) ▸ hz
    · intro hx
      obtain ⟨y,⟨hy,read⟩,_⟩ := backward x hx
      exact (ef Z x).mpr ⟨y,hy,realEq (forward y hy).1 (testReal hx) read⟩
  obtain ⟨b,hb⟩ := baire_nonempty_l (kp_pair_l (ZF.modelsKP native)) native space
  have hbM := (image_member_l (M := N) (N := M) Subtype.val ni nf).mpr hb
  obtain ⟨y,⟨hy,_⟩,_⟩ := backward b.val hbM
  have transW : E.TransitiveSet (j w) := by
    intro a ha b hb
    apply (image_member_l e ei ef).mp
    have ha' := (image_member_l e ei ef).mpr ha
    rw [commute] at ha'
    have out := (lim.omega.transitive (ZF.modelsKP hZF)) (e a) ha' (e b) ((image_member_l e ei ef).mpr hb)
    exact (commute w).symm ▸ out
  obtain ⟨S,tc⟩ := ZF.tc_exists_l (kp_pair_l (ZF.modelsKP hE)) hE Z
  obtain ⟨S₀,tc₀⟩ := ZF.tc_exists_l (kp_pair_l (ZF.modelsKP native)) native B
  have tcImage := Relative.real_tc_image_l (ZF.modelsKP hE) hZF.1 e ei ef transW
    (fun y hy => (forward y hy).1) ⟨y,hy⟩ tc
  rw [realSet] at tcImage
  have tcTest := Relative.real_tc_image_l (ZF.modelsKP native) hZF.1 Subtype.val ni nf
    (space.1.transitive (ZF.modelsKP native))
    (fun x hx => fn0_of_function_l (ZF.modelsKP native) ((space.2 x).mp hx)) ⟨b,hb⟩ tc₀
  have seedEq : e S = S₀.val := tc_unique_l hZF.1 tcImage tcTest
  have layers ξ (ordinal : E.IsOrdinal ξ) : ∃ α : N.Domain, ∃ W : E.Domain, ∃ W₀ : N.Domain,
      N.IsOrdinal α ∧ M.mem α.val θ ∧ e ξ = α.val ∧
      Relative.Ja_d S ξ W ∧ Relative.Ja_d S₀ α W₀ ∧ e W = W₀.val := by
    obtain ⟨k,_,base,_,ordinals⟩ := height
    obtain ⟨α,_,kα,owned,bound⟩ := ordinals ξ ordinal
    have index : e ξ = α.val := kα ▸ fixed α (k α) (base α)
    let α₀ : N.Domain := ⟨α.val,inside α.val owned⟩
    have ordM : M.IsOrdinal α.val := index ▸ image_ord_l hE hZF e ei ef ordinal
    have ordN : N.IsOrdinal α₀ := by
      let ρ : Env N 1 := ⟨fun _ => α₀,fun _ => α₀⟩
      exact (KP.ord0_sat_l (ZF.modelsKP native) ρ .newest).mp
        ((delta0_image_l (M := N) (N := M) Subtype.val ni nf (KP.ord0_delta_l .newest) ρ).mpr
          ((KP.ord0_sat_l (ZF.modelsKP hZF) (image_env_l (M := N) (N := M) Subtype.val ρ) .newest).mpr ordM))
    obtain ⟨W,W₀,layer,layer₀,common⟩ := Relative.ja_common_layer_l
      (ZF.models_kpi_l hE) (ZF.models_kpi_l native) (ZF.models_kpi_l hZF)
      e ei ef (Subtype.val : N.Domain → M.Domain) ni nf seedEq index ordinal ordN
    exact ⟨α₀,W,W₀,ordN,bound,index,
      layer,layer₀,common⟩
  refine ⟨r,Z,S,S₀,name,value,tc,⟨space,tc₀⟩,e,ei,ef,fixed,realSet,seedEq,layers,
    ZF.models_kpi_l hE,?_⟩
  exact Relative.la_common_transport_l I model native trans (ZF.models_kpi_l hE) tc.1
    (Relative.la_transitive_l S (ZF.models_kpi_l hE) tc.1 (Relative.la_seed_l S (ZF.models_kpi_l hE)) tc.2.1)
    ⟨space,tc₀⟩ e ei ef realSet (by
      intro ξ ordinal
      obtain ⟨α,W,W₀,_,_,_,layer,layer₀,common⟩ := layers ξ ordinal
      exact ⟨α,W,W₀,layer,layer₀,common⟩)

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原吸收运行中的 8.6 及共同层真值上传

各出发行使用原记录的全乘积、冻结前缀和泛型。原返回生成滤子兑现已接受
条件的极限像；原极限腿固定 ω 的全部成员。由此搬运原断言和指定参数，
再用同一吸收扩张已经构造的共同 Jensen 层上传。
原行坐标直接量化背景对象；共同模型独立于保存原运行的测试壳。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF) {c K R : M.Domain}
  (model : Smem_d (kp_pair_l (ZF.modelsKP hZF)) c K R)
  (native : (smdl_structure_l (kp_pair_l (ZF.modelsKP hZF)) (R := R) model.1.2.1).Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Ab_truth_d (ω B : (smdl_structure_l I (R := R) model.1.2.1).Domain)
    (hΩ : M.IsOmega ω.val) (F : M.Domain) : Prop :=
  ∀ i r (v : Fin 26 → M.Domain),
    Rd_entry_d i r F → Rt_tuple_d v r →
    ∃ data : Ab_product_data_d I ω.val v,
    let N := smdl_structure_l I (R := v 2) data.model.1.2.1
    let hN := ZFC.models_zf_l (data.theory.native_l I hZF hΩ)
    ∀ {n} (φ : Formula 1 n), φ.FreeClosed → ∀ x : Fin n → M.Domain,
      Fp_truth_d hN (Subtype.val : N.Domain → M.Domain)
        ⟨ω.val,data.inside.1⟩ ⟨v 4,data.inside.2.1⟩ ⟨v 5,data.inside.2.2.1⟩
        ⟨v 6,data.inside.2.2.2.1⟩ ⟨v 8,data.inside.2.2.2.2.2.1⟩
        (fun p => M.mem p.val (v 11)) φ x →
      ∃ b : (Relative.lr_model_l native).Domain, b.val = B ∧
      ∃ y : Fin n → (Relative.lr_model_l native).Domain,
        (∀ k, (y k).val.val = x k) ∧ Sr_truth_d b φ y

theorem Ab_limit_d.truth_l
    {ω B : (smdl_structure_l I (R := R) model.1.2.1).Domain}
    {P₀ cY Y S C U θ F d X V J σ A Q T H H₀ : M.Domain}
    (run : Ab_run_d I P₀ ω.val cY Y S F) (ctx : Ab_return_order_d F C U)
    (filter : Ab_filter_d F C U H₀)
    (lim : Ab_limit_d hZF ω.val cY Y F C U d X V J σ A Q T)
    (generic : Gset_d Q T Q X H)
    (members : ∀ p, M.mem p H ↔ M.mem p Q ∧ ∃ z, Rd_entry_d p z σ ∧ M.mem z H₀)
    (jensen : Ab_jensen_d hZF model native ω B θ lim H) :
    Ab_truth_d hZF model native ω B lim.omega F := by
  intro i r v ir vr
  have frame := (run.queues _ _ _ ir vr).frame
  have data : Ab_product_data_d I ω.val v :=
    ⟨frame.model,frame.theory,frame.transitive,
      ⟨frame.inside.1,frame.inside.2.1,frame.inside.2.2.1,frame.inside.2.2.2.1,
        frame.inside.2.2.2.2.1,frame.inside.2.2.2.2.2.1,frame.inside.2.2.2.2.2.2.1⟩,frame.kernel⟩
  refine ⟨data,?_⟩
  dsimp only
  let N := smdl_structure_l I (R := v 2) data.model.1.2.1
  have hN := ZFC.models_zf_l (data.theory.native_l I hZF lim.omega)
  let L := smdl_structure_l I (R := V) lim.model.1.2.1
  have hL := ZFC.models_zf_l (lim.theory.native_l I hZF lim.omega)
  let w : N.Domain := ⟨ω.val,data.inside.1⟩
  let a : N.Domain := ⟨v 4,data.inside.2.1⟩
  let p : N.Domain := ⟨v 5,data.inside.2.2.1⟩
  let t : N.Domain := ⟨v 6,data.inside.2.2.2.1⟩
  let m : N.Domain := ⟨v 7,data.inside.2.2.2.2.1⟩
  let b : N.Domain := ⟨v 8,data.inside.2.2.2.2.2.1⟩
  let s : N.Domain := ⟨v 9,data.inside.2.2.2.2.2.2⟩
  let G : L.Domain → Prop := fun p => M.mem p.val H
  obtain ⟨clock,alphabet,product,stage⟩ := (ab_kernel_read_l I data.model data.transitive hN w a p t m b s).mp data.kernel
  have hm : N.mem m w := (data.model.2 m.val w.val).mpr ⟨m.property,w.property,
    frame.index⟩
  obtain ⟨W,range⟩ := ZF.exists_range_of_setFunction hN (kp_pair_l (ZF.modelsKP hN)) alphabet.function alphabet.domain
  have fa : N.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hN)) a w W :=
    ⟨alphabet.function,alphabet.domain,fun k hk => by
      obtain ⟨z,kz⟩ := (alphabet.domain k).mp hk
      exact ⟨z,(range z).mpr ⟨k,kz⟩,kz⟩⟩
  obtain ⟨j,ij⟩ := (lim.domain i).mp (run.function.bound_l ir).1
  obtain ⟨leg,_,pQ,tT⟩ := lim.rows i r _ j ir vr ij
  obtain ⟨e,elem,values⟩ := leg.project_l I hZF lim.omega data.model.1 lim.model.1
  have ew : e w = (⟨ω.val,lim.inside.1⟩ : L.Domain) := Subtype.ext
    (leg.1.1.1.2 _ _ _ (values w) (leg.omega_l I hZF lim.omega data.transitive lim.transitive data.model lim.model data.inside.1))
  have ep : e p = (⟨Q,lim.inside.2.2.1⟩ : L.Domain) := Subtype.ext (leg.1.1.1.2 _ _ _ (values p) pQ)
  have et : e t = (⟨T,lim.inside.2.2.2⟩ : L.Domain) := Subtype.ext (leg.1.1.1.2 _ _ _ (values t) tT)
  have fixed (q : N.Domain) (hq : N.mem q w) : (e q).val = q.val := leg.1.1.1.2 _ _ _ (values q)
    (leg.natural_l hZF lim.omega data.transitive lim.transitive data.model lim.model data.inside.1 q.val
      ((data.model.2 q.val w.val).mp hq).2.2)
  have accept (q : N.Domain) (hq : M.mem q.val (v 11)) : G (e q) :=
    lim.condition_l hZF run ctx filter members ir vr ij hq (values q)
  have g : Generic_d L (e p) (e t) (e p) G := by
    rw [ep,et]
    exact ((lim.model.generic_code_l I hZF.1 lim.transitive (ZF.modelsKP hL)
      ⟨Q,lim.inside.2.2.1⟩ ⟨T,lim.inside.2.2.2⟩ ⟨Q,lim.inside.2.2.1⟩ H).mp generic).2
  have product' : Fp_product_d hL (e w) ⟨A,lim.inside.2.1⟩ (e p) (e t) := by
    simpa only [ew,ep,et] using lim.product
  let E := extension_l L hL (e p) (e t) (e p) G
  -- 只重写条件域的已证等式，保留原名字商、背景坍塌及共同层运输。
  have pack : ∃ r' : L.Domain, ∃ Z S' : E.Domain,
      Rp_name_d hL (e w) ⟨A,lim.inside.2.1⟩ (e p) r' ∧ Qval_d L (e p) (e t) (e p) G r' Z ∧ Tc_d Z S' ∧
      ∃ f : E.Domain → M.Domain, Function.Injective f ∧
        (∀ a y, M.mem y (f a) ↔ ∃ b, E.mem b a ∧ f b = y) ∧
        (∀ a z, Gval_d L (e p) (e t) (e p) G a z → f z = a.val) ∧
        ∃ hE : E.Models KPi, Relative.La_transport_d I model native hE S' Z B f := by
    dsimp only [E]
    rw [ep,et,ew]
    obtain ⟨r',Z,S',_,name,value,tc,_,f,fi,ff,base,_,_,_,hE,transport⟩ := jensen
    exact ⟨r',Z,S',name,value,tc,f,fi,ff,base,hE,transport⟩
  obtain ⟨r',Z,S',name,value,tc,f,fi,ff,base,hE,transport⟩ := pack
  intro n φ hc x truth
  obtain ⟨y,images,moved⟩ := truth.transfer_l hN hL (ZF.modelsKP hZF) e elem Subtype.val
    (fun _ _ eq => Subtype.ext eq) (smem_full_l I data.model data.transitive) Subtype.val
    clock fa product stage hm g accept (congrArg Subtype.val ew) fixed product' name value f fi ff base hc
  obtain ⟨b',bB,z,params,final⟩ := transport.truth_l I model native tc hc moved
  exact ⟨b',bB,z,fun k => (params k).trans (images k),final⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原返回目标中的实际共同 Jensen 层

返回目标的完整 ZF 来自原行嵌入。实数集属于同一目标，每个扩张序数
的背景代表也属于该目标，因此共同层在已实现的完整模型中构造。
测试壳只提供原记录、传递包含及实际运行，不承担完整集合论模式。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Ab_common_d {cY Y S : M.Domain} (target : Smem_d I cY Y S) (P ω F : M.Domain) : Prop :=
  ∃ native : (smdl_structure_l I (R := S) target.1.2.1).Models ZF,
  ∃ Ω B : (smdl_structure_l I (R := S) target.1.2.1).Domain,
    Ω.val = ω ∧ Rb_reals_d P ω B.val ∧
    ∃ θ C U H₀ d X V J σ A Q T H, M.mem θ P ∧ Ab_return_order_d F C U ∧ Ab_filter_d F C U H₀ ∧
    ∃ lim : Ab_limit_d hZF Ω.val cY Y F C U d X V J σ A Q T,
      Gset_d Q T Q X H ∧
      (∀ p, M.mem p H ↔ M.mem p Q ∧ ∃ z, Rd_entry_d p z σ ∧ M.mem z H₀) ∧
      (∀ x, Ab_limit_real_d hZF lim H x ↔ M.mem x B.val) ∧
      Ab_prefix_reals_d hZF lim H B.val ∧
      (∀ α, M.mem α X → M.IsOrdinal α → M.mem α θ) ∧
      Ab_extension_height_d hZF lim H θ ∧ Ab_real_name_d hZF lim H B.val ∧
      Ab_jensen_d hZF target native Ω B θ lim H ∧
      Ab_truth_d hZF target native Ω B lim.omega F

theorem Ab_run_d.common_l {c P R : M.Domain} (model : Smem_d I c P R) (trans : M.TransitiveSet P)
    {ω cY Y S : (smdl_structure_l I (R := R) model.1.2.1).Domain} {F T₀ Q₀ G₀ U₀ : M.Domain}
    (hΩ : M.IsOmega ω.val) (run : Ab_run_d I P ω.val cY.val Y.val S.val F)
    (system : Wi_state_d I ω.val ω.val T₀ Q₀ G₀ cY.val Y.val S.val U₀)
    (records : ∀ i r (v : Fin 26 → M.Domain), Rd_entry_d i r F → Rt_tuple_d v r →
      Wi_keep_d (v 23) (v 24) (v 25) Q₀ G₀ U₀) :
    Ab_common_d hZF run.target P ω.val F := by
  obtain ⟨o,_,ho⟩ := hΩ.1.1
  obtain ⟨r₀,_,first⟩ := run.function.2.1 o ho
  obtain ⟨v₀,vr₀,_⟩ := run.columns_l hZF.1 model trans first
  have frame := (run.queues o r₀ v₀ first vr₀).frame
  obtain ⟨native,hwY⟩ := frame.target_l hZF hΩ run.target run.transitive
  obtain ⟨B,_,hB,_,space,_⟩ := run.seed
  let N := smdl_structure_l I (R := S.val) run.target.1.2.1
  let Ω : N.Domain := ⟨ω.val,hwY⟩
  let b : N.Domain := ⟨B,hB⟩
  have clock : N.IsOmega Ω := by
    let nx : Nonempty {x // M.mem x Y.val} := ⟨Ω⟩
    let ρ : Env (rt_model_l Y.val nx) 1 := ⟨fun _ => ⟨ω.val,hwY⟩,fun _ => ⟨ω.val,hwY⟩⟩
    have old := (Formula.satisfies_isOmega_iff ρ .newest).mpr
      (rt_omega_l run.transitive nx hZF.1 ⟨ω.val,hwY⟩ hΩ)
    exact (Formula.satisfies_isOmega_iff _ .newest).mp ((smem_formula_l I run.target nx _ ρ).mp old)
  have nativeSpace : Baire_d (kp_pair_l (ZF.modelsKP native)) Ω b := by
    refine ⟨clock,fun x => ?_⟩
    have hx := trans Y.val Y.property x.val x.property
    exact (smem_member_l I run.target.1 run.target.2 x b).trans ((space x.val).trans
      ((and_iff_right hx).trans ((smem_fn0_l I hZF.1 run.target run.transitive Ω Ω x).symm.trans
        ⟨fn0_function_l (ZF.modelsKP native),fn0_of_function_l (ZF.modelsKP native)⟩)))
  obtain ⟨C,U,ctx⟩ := run.return_order_l hZF model trans hΩ
  obtain ⟨H₀,filter⟩ := run.filter_l hZF model trans hΩ ctx
  obtain ⟨d,X,V,J,σ,A,Q,T,lim⟩ := run.limit_l hZF model trans hΩ ctx system records
  obtain ⟨H,generic,members⟩ := lim.generic_l hZF model trans run ctx filter
  have same := lim.reals_l hZF model trans space run ctx filter generic members
  obtain ⟨θ,hθ,bound⟩ := run.height
  have height := lim.extension_height_l hZF run.target run.transitive bound generic
  have names := lim.real_name_l hZF generic same
  have common := lim.jensen_l hZF run.target native run.transitive (fun _ h => h) nativeSpace generic names height
  exact ⟨native,Ω,b,rfl,space,θ,C.val,U.val,H₀,d,X,V,J,σ,A,Q,T,H,hθ,ctx,filter,lim,
    generic,members,same,lim.prefix_values_l hZF generic (fun x => (same x).mp),
    lim.height_l hZF run.target run.transitive bound,height,names,common,
    lim.truth_l hZF run.target native run ctx filter generic members common⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原返回目标到测试壳的实际公式出口

共同层中的同一见证沿 Y⊆P 运输，返回测试壳对原 dr_m 的满足关系。
所有原行坐标继续量化背景对象，测试壳不承担 ZF 或 KP。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Ab_upload_d {c P R : M.Domain} (model : Smem_d I c P R)
    (ω : (smdl_structure_l I (R := R) model.1.2.1).Domain) (hw : M.IsOmega ω.val) (F : M.Domain) : Prop :=
  ∃ B : (smdl_structure_l I (R := R) model.1.2.1).Domain, Rb_reals_d P ω.val B.val ∧
  ∀ i r (v : Fin 26 → M.Domain), Rd_entry_d i r F → Rt_tuple_d v r →
    ∃ data : Ab_product_data_d I ω.val v,
    let N := smdl_structure_l I (R := v 2) data.model.1.2.1
    let hN := ZFC.models_zf_l (data.theory.native_l I hZF hw)
    ∀ {n} (φ : Formula 1 n), φ.FreeClosed → ∀ x : Fin n → M.Domain,
      Fp_truth_d hN (Subtype.val : N.Domain → M.Domain)
        ⟨ω.val,data.inside.1⟩ ⟨v 4,data.inside.2.1⟩ ⟨v 5,data.inside.2.2.1⟩
        ⟨v 6,data.inside.2.2.2.1⟩ ⟨v 8,data.inside.2.2.2.2.2.1⟩ (fun p => M.mem p.val (v 11)) φ x →
      ∃ y : Fin n → (smdl_structure_l I (R := R) model.1.2.1).Domain, (∀ k, (y k).val = x k) ∧
        Formula.satisfies (⟨Fin.cases B y,fun _ => B⟩ : Env _ (n+1))
          (Relative.dr_m φ .newest (fun k => .bound k.succ))

theorem Ab_common_d.upload_l {c P R : M.Domain} (model : Smem_d I c P R) (trans : M.TransitiveSet P)
    {ω cY Y S : (smdl_structure_l I (R := R) model.1.2.1).Domain} {F : M.Domain}
    (target : Smem_d I cY.val Y.val S.val) (yt : M.TransitiveSet Y.val) (hw : M.IsOmega ω.val)
    (common : Ab_common_d hZF target P ω.val F) : Ab_upload_d hZF model ω hw F := by
  rcases common with ⟨native,Ω,B,eω,space,common⟩
  rcases common with ⟨θ,C,U,H₀,d,X,V,J,σ,A,Q,T,H,_,_,_,lim,_,_,_,_,_,_,_,jensen,truth⟩
  obtain ⟨_,_,_,_,_,_,_,seed,_⟩ := jensen
  let N := smdl_structure_l I (R := S.val) target.1.2.1
  let L := smdl_structure_l I (R := R) model.1.2.1
  let e : N.Domain → L.Domain := fun a => ⟨a.val,trans Y.val Y.property a.val a.property⟩
  have inj : Function.Injective e := fun _ _ eq => Subtype.ext (congrArg (fun z : L.Domain => z.val) eq)
  have full (a : N.Domain) (y : L.Domain) : L.mem y (e a) ↔ ∃ z, N.mem z a ∧ e z = y := by
    constructor
    · intro hy
      have old := (smem_member_l I model.1 model.2 y (e a)).mp hy
      let z : N.Domain := ⟨y.val,yt a.val a.property y.val old⟩
      exact ⟨z,(smem_member_l I target.1 target.2 z a).mpr old,Subtype.ext rfl⟩
    · rintro ⟨z,hz,rfl⟩
      exact (smem_member_l I model.1 model.2 (e z) (e a)).mpr ((smem_member_l I target.1 target.2 z a).mp hz)
  have ext := smem_ext_l I model.1 model.2 trans hZF.1
  have output : Ab_upload_d hZF model (e Ω) lim.omega F := by
    refine ⟨e B,(show Rb_reals_d P Ω.val B.val from eω.symm ▸ space),?_⟩
    intro i r v ir vr
    obtain ⟨data,all⟩ := truth i r v ir vr
    refine ⟨data,?_⟩
    dsimp only
    intro n φ hc x accepted
    obtain ⟨b,bB,y,images,old⟩ := all φ hc x accepted
    have decoded := Relative.lr_truth_decode_l native seed.1 hc bB old
    exact ⟨fun k => e (y k).val,images,
      Relative.Dr_truth_d.formula_image_l (ZF.modelsKP native) ext e inj full
        (seed.1.1.transitive (ZF.modelsKP native))
        (fun f hf => fn0_of_function_l (ZF.modelsKP native) ((seed.1.2 f).mp hf))
        (baire_nonempty_l (kp_pair_l (ZF.modelsKP native)) native seed.1) hc decoded⟩
  simpa only [show e Ω = ω from Subtype.ext eω] using! output

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原吸收运行在有限反射测试壳中的收尾

同一原记录产生整列相容历史、公平调度和全乘积泛型。共同 Jensen 层
在原返回目标中构造，再把原断言的实际见证送入测试壳。这里不要求
测试壳满足 ZF、KP，亦不要求壳内存在完整的秩层或 L(ℝ)。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 原运行、并历史、共同层及原公式出口共用同一个实际直接极限。 -/
theorem Ab_run_d.finish_l {c P R : M.Domain} (model : Smem_d I c P R) (trans : M.TransitiveSet P)
    {ω cY Y S : (smdl_structure_l I (R := R) model.1.2.1).Domain}
    {F : M.Domain} (hΩ : M.IsOmega ω.val) (run : Ab_run_d I P ω.val cY.val Y.val S.val F) :
    ∃ D H T Q G U, Wi_history_d hZF ω.val cY.val Y.val S.val ω.val D H ∧
      Wi_state_d I ω.val ω.val T Q G cY.val Y.val S.val U ∧
      (∀ i r (v : Fin 26 → M.Domain), Rd_entry_d i r F → Rt_tuple_d v r →
        Wi_at_d H i (v 22) (v 23) (v 24) (v 25)) ∧
      (∀ i T' Q' G' U', Wi_at_d H i T' Q' G' U' → Wi_keep_d Q' G' U' Q G U) ∧
      (∀ i d X V, Rd_entry_d i d Q → Smdl_d I d X V → Zc_model_d I ω.val d X V) ∧
      (∀ k, M.mem k ω.val → ∃ i r, ∃ v : Fin 26 → M.Domain,
        Rd_entry_d i r F ∧ Rt_tuple_d v r ∧ v 18 = k ∧ v 7 = v 20 ∧
        M.mem (v 21) (v 19) ∧ M.mem (v 21) (v 11)) ∧
      Ab_common_d hZF run.target P ω.val F ∧ Ab_upload_d hZF model ω hΩ F := by
  obtain ⟨D,H,T,Q,G,U,hist,diagram,trace,keep,cert⟩ := ab_outer_history_l hZF model trans hΩ run
  have common := run.common_l hZF model trans hΩ diagram
    (fun i r v ir vr => keep i (v 22) (v 23) (v 24) (v 25) (trace i r v ir vr))
  exact ⟨D,H,T,Q,G,U,hist,diagram,trace,keep,cert,run.fair_l hZF model trans hΩ,
    common,common.upload_l hZF model trans run.target run.transitive hΩ⟩

end YesMetaZFC.SetTheory.LargeCardinal
