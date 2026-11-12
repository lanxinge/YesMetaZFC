import YesMetaZFC.SetTheory.LargeCardinal.Demand.HistoryConstruction
import YesMetaZFC.Model.SetTheory.Types.SubtypeReflect
import YesMetaZFC.Model.SetTheory.Types.DropEmbedding
import YesMetaZFC.Model.SetTheory.Relations.NativeSmemSlice
import YesMetaZFC.Model.SetTheory.Relations.OmegaCut
import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawOwnedCopy
import YesMetaZFC.SetTheory.LargeCardinal.Extender.LocalRead
import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawCoherence
import YesMetaZFC.SetTheory.LargeCardinal.Cardinals.WoodinInitial
import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawAlphabet

/-! # 7.1 完整回答从传递证书层向上读取

dcp 使用源 q、n 两个元数，子类型使用独立的目标 m。全部七个程序槽
及三条查询成员保持原对象；证书层只需传递性与配对闭包，外模型只需 KP。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hKP : M.Models KP) {X : M.Domain} (hX : M.TransitiveSet X)
  (nx : Nonempty {x // M.mem x X})
  (pair : ∀ a b, M.mem a X → M.mem b X → ∃ p, M.mem p X ∧ Pair_d M p a b)
local notation "N" => rt_model_l X nx
include hX pair

theorem td_reply_source_l {d} (ρ : Env N d)
    (ω q n m κ τ U E Dw u w b z pp pb ph : Term d) (σ : Fin 7 → Term d)
    (valid : Formula.satisfies ρ (td_reply_m ω q n m κ τ U E Dw u w b z pp pb ph σ)) :
    Td_reply_d (kp_pair_l hKP) (ω.eval ρ).val (q.eval ρ).val (n.eval ρ).val (m.eval ρ).val
      (κ.eval ρ).val (τ.eval ρ).val (U.eval ρ).val (E.eval ρ).val (Dw.eval ρ).val (u.eval ρ).val
      (w.eval ρ).val (b.eval ρ).val (z.eval ρ).val (pp.eval ρ).val (pb.eval ρ).val (ph.eval ρ).val
      (fun i => (σ i).eval ρ |>.val) := by
  let ε := Definitional.Env.substitute ρ (fun i => [ω,q,n,m,κ,τ,U,E,Dw,u,w,b,z,pp,pb,ph,
    σ 0,σ 1,σ 2,σ 3,σ 4,σ 5,σ 6].get i)
  let s : Fin 7 → Term 23 := Fin.cases (.bound 16) (Fin.cases (.bound 17) (Fin.cases (.bound 18)
    (Fin.cases (.bound 19) (Fin.cases (.bound 20) (Fin.cases (.bound 21) (fun _ => .bound 22))))))
  simp only [td_reply_m,Formula.satisfies_bind,td_reply0_m,Formula.satisfies_conj_iff,
    Formula.satisfies_exists_iff,Formula.satisfies_subset_iff,
    Formula.satisfies_mem_iff,Definitional.Term.eval_weaken] at valid
  obtain ⟨sub,v,drop,code,pending,bound,height⟩ := valid
  have subset : M.MemberSubset (w.eval ρ).val (Dw.eval ρ).val :=
    fun x hx => sub ⟨x,hX (w.eval ρ).val (w.eval ρ).property x hx⟩ hx
  have drop := (td_dcp_source_l hKP.1 (KP.exists_pair hKP) hX nx pair _ _ _ _ _ _).mp drop
  have code := ts_subtype_source_l hKP hX nx _ _ _ _ _ _ _ _ _ _ _ _ code
  simp only [Definitional.Term.eval_weaken,Definitional.Term.eval_newest] at drop code
  have eq : (fun i => (s i).eval ε |>.val) = (fun i => (σ i).eval ρ |>.val) := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))))))) i
  have code : Ts_subtype_d (ω.eval ρ).val (q.eval ρ).val (κ.eval ρ).val (τ.eval ρ).val
      (m.eval ρ).val (U.eval ρ).val (w.eval ρ).val (b.eval ρ).val (fun i => (s i).eval ε |>.val)
      (z.eval ρ).val v.val := code
  exact ⟨subset,v.val,drop,eq ▸ code,pending,bound,height⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 23 槽 demanding 回答沿同一代表池进入原后继

完整值域与前驱图先搬运配对闭包，再搬运 7.1 回答的全部量词。
目标在自己的原关系中读出完整回答，不对原载体增加传递性或外部良基性。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

theorem td_reply_raw_image_l {N R P S Γ t : M.Domain}
    (nx : ∃ x, M.mem x N) (ny : ∃ y, M.mem y P)
    (hP : (smdl_structure_l I (R := S) ny).Models KP)
    (B : (smdl_structure_l I (R := R) nx).Domain)
    (H : (smdl_structure_l I (R := S) ny).Domain)
    (pair : ∀ a b, (smdl_structure_l I (R := R) nx).mem a B →
      (smdl_structure_l I (R := R) nx).mem b B →
      ∃ p, (smdl_structure_l I (R := R) nx).mem p B ∧ Pair_d (smdl_structure_l I (R := R) nx) p a b)
    (nb : Nonempty {x // (smdl_structure_l I (R := R) nx).mem x B})
    (ρ : Env (rt_model_l B nb) 23) (reply : Formula.satisfies ρ td_reply0_m)
    (carrier : ∀ x, M.mem x Γ ↔ M.mem x N ∧ M.PairMember I x B.val R)
    (ft : M.IsSetInjectionFromTo I t Γ P)
    (image : ∀ E, M.PairMember I E H.val S ↔ ∃ x, M.mem x Γ ∧ M.PairMember I x E t)
    (pred : ∀ x E, M.PairMember I x E t → ∀ y,
      M.PairMember I y E S ↔ ∃ a, M.PairMember I a x R ∧ M.PairMember I a y t) :
    ∃ η : Env (smdl_structure_l I (R := S) ny) 23,
      (∀ i, M.PairMember I (ρ.bound i).val.val (η.bound i).val t) ∧ Formula.satisfies η td_reply0_m := by
  let P₀ := smdl_structure_l I (R := S) ny
  obtain ⟨ht,pairs⟩ := rr_native_pair_l I nx ny B H pair carrier ft image pred
  obtain ⟨v, hv⟩ := Classical.axiomOfChoice (fun i : Fin 23 => ft.1.2.2 (ρ.bound i).val.val
    ((carrier _).mpr ⟨(ρ.bound i).val.property, (ρ.bound i).property⟩))
  have vh i : P₀.mem ⟨v i, (hv i).1⟩ H :=
    (image (v i)).mpr ⟨_, ft.1.input_mem_of_pairMember (hv i).2, (hv i).2⟩
  let nh : Nonempty {x : P₀.Domain // P₀.mem x H} := ⟨⟨⟨v 0, (hv 0).1⟩, vh 0⟩⟩
  let ε : Env (rt_model_l H nh) 23 :=
    ⟨fun i => ⟨⟨v i, (hv i).1⟩, vh i⟩, fun _ => ⟨⟨v 0, (hv 0).1⟩, vh 0⟩⟩
  have transferred := (rr_native_slice_l I nx ny B H nb nh carrier ft image pred
    td_reply0_m td_reply0_closed_l ρ ε (fun i => (hv i).2)).mp reply
  let slots : Fin 7 → Term 23 := Fin.cases (.bound 16) (Fin.cases (.bound 17) (Fin.cases (.bound 18)
    (Fin.cases (.bound 19) (Fin.cases (.bound 20) (Fin.cases (.bound 21) (fun _ => .bound 22))))))
  have actual := td_reply_source_l hP ht nh pairs ε (.bound 0) (.bound 1) (.bound 2) (.bound 3)
    (.bound 4) (.bound 5) (.bound 6) (.bound 7) (.bound 8) (.bound 9) (.bound 10)
    (.bound 11) (.bound 12) (.bound 13) (.bound 14) (.bound 15) slots transferred
  let η := image_env_l Subtype.val ε
  refine ⟨η, fun i => (hv i).2, ?_⟩
  apply (td_reply_sat_l hP η (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4)
    (.bound 5) (.bound 6) (.bound 7) (.bound 8) (.bound 9) (.bound 10) (.bound 11)
    (.bound 12) (.bound 13) (.bound 14) (.bound 15) slots).mpr
  simpa only [η, @eval_image_env_l (rt_model_l H nh) P₀ Subtype.val] using actual

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 完整双图回答回到同一有界证书层

源内分离得到的投影由唯一性识别为原回答的同一 dcp；名字域也在源内
实际构造。随后回收 subtype 的全部见证，保留源 q、n 与目标 m 三个元数。
有界层只需已有 Sc_theory，不假定它满足 KP、ZF 或 ZFC。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem td_reply_reflect_l {ω c X R : M.Domain} (hω : M.IsOmega ω) (hX : M.TransitiveSet X)
    (model : Smem_d I c X R) (theory : Sc_theory_d I ω X R) (nx : Nonempty {x // M.mem x X})
    {d} (ρ : Env (rt_model_l X nx) d)
    (o q n m κ τ U E Dw u w b z pp pb ph : Term d) (σ : Fin 7 → Term d)
    (valid : Td_reply_d I (o.eval ρ).val (q.eval ρ).val (n.eval ρ).val (m.eval ρ).val
      (κ.eval ρ).val (τ.eval ρ).val (U.eval ρ).val (E.eval ρ).val (Dw.eval ρ).val (u.eval ρ).val
      (w.eval ρ).val (b.eval ρ).val (z.eval ρ).val (pp.eval ρ).val (pb.eval ρ).val (ph.eval ρ).val
      (fun i => (σ i).eval ρ |>.val)) :
    Formula.satisfies ρ (td_reply_m o q n m κ τ U E Dw u w b z pp pb ph σ) := by
  let N := rt_model_l X nx
  let ε := Definitional.Env.substitute ρ (fun i => [o,q,n,m,κ,τ,U,E,Dw,u,w,b,z,pp,pb,ph,
    σ 0,σ 1,σ 2,σ 3,σ 4,σ 5,σ 6].get i)
  let s : Fin 7 → Term 23 := Fin.cases (.bound 16) (Fin.cases (.bound 17) (Fin.cases (.bound 18)
    (Fin.cases (.bound 19) (Fin.cases (.bound 20) (Fin.cases (.bound 21) (fun _ => .bound 22))))))
  obtain ⟨subset,v,drop,subtype,pending,bound,height⟩ := valid
  obtain ⟨v',hv,project⟩ := td_project_source_exists_l hX hZF hω model theory
    (q.eval ρ).property (n.eval ρ).property (E.eval ρ).property (u.eval ρ).property
  have eq := project.unique_l I hZF.1 drop.2
  subst v'
  obtain ⟨A,hA,names⟩ := tn_names_source_l hZF hω hX model theory (q.eval ρ).property (U.eval ρ).property
  let v₀ : N.Domain := ⟨v,hv⟩
  have sub : Formula.satisfies ε (Formula.subset (.bound 10) (.bound 8)) := by
    apply (rt_model_delta_l hX nx (.atom ..) ε).mpr
    apply (Formula.satisfies_subset_iff ..).mpr
    exact subset
  simp only [td_reply_m,Formula.satisfies_bind,td_reply0_m,Formula.satisfies_conj_iff,
    Formula.satisfies_exists_iff,Formula.satisfies_mem_iff,Definitional.Term.eval_weaken]
  refine ⟨sub,v₀,?_,?_,pending,bound,height⟩
  · apply (td_dcp_source_l hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) hX nx
      (theory.algebra_l _ (ZF.modelsKP hZF) hX model).pair ..).mpr
    simp only [Definitional.Term.eval_weaken,Definitional.Term.eval_newest]
    exact drop
  · apply ts_subtype_reflect_l (ZF.modelsKP hZF) hX nx _ _ _ _ _ _ _ _ _ _ _ _ hA (by exact names)
    have eq : (fun i => (s i).eval ε |>.val) = (fun i => (σ i).eval ρ |>.val) := by
      funext i
      exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))))))) i
    have subtype : Ts_subtype_d (o.eval ρ).val (q.eval ρ).val (κ.eval ρ).val (τ.eval ρ).val
        (m.eval ρ).val (U.eval ρ).val (w.eval ρ).val (b.eval ρ).val (fun i => (s i).eval ε |>.val)
        (z.eval ρ).val v := eq.symm ▸ subtype
    simp only [Definitional.Term.eval_weaken,Definitional.Term.eval_newest]
    exact subtype

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 同一次有界塌缩中的完整 demanding 回答

原极限切片的相对秩沿指定超幂搬运，为同一个 B 产生 Sc_theory。
完整 23 槽回答随后回收到 B；源 q、n 和目标 m 分别保存，n 的
有限性由实际 dcp 后继证书产生，不从目标元数推断。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def td_reply_values_d {α : Type u} (ω q n m κ τ U E Dw u w b z pp pb ph : α)
    (σ : Fin 7 → α) : Fin 23 → α :=
  fun i => [ω,q,n,m,κ,τ,U,E,Dw,u,w,b,z,pp,pb,ph,σ 0,σ 1,σ 2,σ 3,σ 4,σ 5,σ 6].get i

/-- 全部几何参数来自给定超幂及同一 owned 池，不另选后继或反射模型。 -/
theorem td_reply_pool_l
    {ω κ δ q n m U E u τ Dw w b z pp pb ph L X K R F c d Y S j κ' U' E' u'
      α β A T B e : M.Domain} {σ : Fin 7 → M.Domain}
    (rankX : V_d I δ X) (source : Ep_source_d I ω κ K X R) (height : M.IsLimitOrdinal δ)
    (loc : It_local_d I ω X R κ L F) (mx : Smem_d I c X R) (my : Smem_d I d Y S)
    (ultra : It_ultra_d I ω κ L F c d j) (critical : Wd_crit_d I X j κ κ')
    (κlimit : M.IsLimitOrdinal κ')
    (iU : Rd_entry_d U U' j) (iE : Rd_entry_d E E' j) (iu : Rd_entry_d u u' j)
    (reply : Td_reply_d I ω q n m κ' τ U' E' Dw u' w b z pp pb ph σ)
    (rank : V_d I α β) (limit : M.IsLimitOrdinal α) (below : M.mem α δ)
    (hU : M.mem U β) (hE : M.mem E β) (hu : M.mem u β)
    (owned : Eb_collapse_d ω κ L K X β F A T B e) (hDwB : M.mem Dw B)
    (hq : M.mem q ω) (hb : M.mem b ω) (hz : M.mem z ω) (hσ : ∀ i, M.mem (σ i) ω) :
    M.TransitiveSet B ∧ (∀ a b, M.mem a B → M.mem b B → ∃ p, M.mem p B ∧ Pair_d M p a b) ∧
    ∃ nb : Nonempty {x // M.mem x B}, ∃ ρ : Env (rt_model_l B nb) 23,
      (∀ i, (ρ.bound i).val = td_reply_values_d ω q n m κ' τ U' E' Dw u' w b z pp pb ph σ i) ∧
      Formula.satisfies ρ td_reply0_m := by
  have family := loc.measures_l hZF source.omega (source.read_source_l hZF) source.code source.theory
    (fun _ D _ hD _ => sc_v_power_l (ZF.modelsKP hZF) height rankX D hD)
  have hj := ultra.elementary_l hZF mx.1 my.1
  have yt := ultra.transitive_l hZF my.1
  have hβX := ZF.v_mem_l I hZF rank rankX below
  have iβ := (owned.image_l hZF source family mx my ultra hβX (v_transitive_l I rank)).1
  have hBY := hj.1.1.output_mem_of_pairMember iβ
  obtain ⟨a,_,ia⟩ := hj.1.1.2.2 α (KP.v_ordinal_subset_l (ZF.modelsKP hZF) rankX α below)
  obtain ⟨Z,f,hZ,hf,history,_⟩ := vr_source_l hZF rankX height below rank
  have relative : Vr_d X α β := ⟨Z,f,hZ,hf,fun x _ => history x⟩
  have rankB := (hj.hierarchy_l hZF source.omega source.transitive yt mx my ia iβ).mp relative
  have limitB := (hj.limit_l hZF source.omega source.transitive yt mx my ia).mp limit
  have bt := rankB.transitive_l yt hBY
  have theory := source.theory.map_l I hZF source.omega mx.1 my.1 hj
  obtain ⟨K',target⟩ := source.successor_l hZF mx my yt hj
    (hj.1.1.output_mem_of_pairMember critical.image)
    (source.omega.subset_limitOrdinal (ZF.modelsKP hZF) κlimit)
    (sc_ordinal_small_l hZF source.omega yt my theory
      (hj.1.1.output_mem_of_pairMember critical.image) κlimit.1)
  have hU' := (hj.member_l I hZF source.omega mx my iU iβ).mp hU
  have hE' := (hj.member_l I hZF source.omega mx my iE iβ).mp hE
  have hu' := (hj.member_l I hZF source.omega mx my iu iβ).mp hu
  have data := reply
  obtain ⟨_,v,drop,⟨_,_,code,query,_⟩,hpp,hpb,hph⟩ := data
  obtain ⟨hw,hm,hqU,hτ,hκ,hω⟩ := query.constants
  obtain ⟨n₀,sn,hn₀⟩ := source.omega.1.2 q hq
  have hn : M.mem n ω := sn.eq hZF.1 drop.1 ▸ hn₀
  have low x (hx : M.mem x U') := bt U' hU' x hx
  have small x (hx : M.mem x ω) := bt ω (low ω hω) x hx
  let values : Fin 23 → M.Domain := td_reply_values_d ω q n m κ' τ U' E' Dw u' w b z pp pb ph σ
  have members : ∀ i, M.mem (values i) B := by
    simp only [Fin.forall_fin_succ]
    exact ⟨low ω hω,low q hqU,small n hn,low m hm,low κ' hκ,low τ hτ,hU',hE',hDwB,hu',
      low w hw,small b hb,small z hz,bt w (low w hw) pp hpp,bt w (low w hw) pb hpb,
      bt w (low w hw) ph hph,small _ (hσ 0),small _ (hσ 1),small _ (hσ 2),small _ (hσ 3),
      small _ (hσ 4),small _ (hσ 5),small _ (hσ 6),fun i => Fin.elim0 i⟩
  obtain ⟨cB,RB,modelB⟩ := smdl_membership_l I hZF ⟨ω,members 0⟩
  have theoryB := target.rank_theory_l hZF hBY rankB limitB modelB
  let nb : Nonempty {x // M.mem x B} := ⟨⟨ω,members 0⟩⟩
  let ρ : Env (rt_model_l B nb) 23 := ⟨fun i => ⟨values i,members i⟩,fun _ => ⟨ω,members 0⟩⟩
  let slots : Fin 7 → Term 23 := Fin.cases (.bound 16) (Fin.cases (.bound 17) (Fin.cases (.bound 18)
    (Fin.cases (.bound 19) (Fin.cases (.bound 20) (Fin.cases (.bound 21) (fun _ => .bound 22))))))
  have eq : (fun i => ((slots i).eval ρ).val) = σ := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))))))) i
  refine ⟨bt,(theoryB.algebra_l _ (ZF.modelsKP hZF) bt modelB).pair,nb,ρ,fun _ => rfl,?_⟩
  apply td_reply_reflect_l hZF source.omega bt modelB theoryB nb ρ
    (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 6) (.bound 7)
    (.bound 8) (.bound 9) (.bound 10) (.bound 11) (.bound 12) (.bound 13) (.bound 14) (.bound 15) slots
  exact eq.symm ▸ reply

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 指定原后继中的同池 23 槽回答

只解包一次原施加证书。其实际 owned 池先回收完整回答，再由同一池图的
完整前驱搬到原后继；源元数 q、n 与目标元数 m 分别连接到同一原生 ω。
所属模型只提供原生理论，不假设它向原后继存在整体嵌入。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Er_rank_cut_at_d.demand_reply_l
    {Ω c₀ X₀ R₀ c Y S q₀ Γ k₀ N R z₀ cN
      Ls Js Os Zs As ps Ts Vs rs ct P Rp jt qt p₀ : M.Domain}
    (hΩ : M.IsOmega Ω) (root : Zc_model_d I Ω c₀ X₀ R₀)
    (nx : ∃ x, M.mem x N)
    (native : (smdl_structure_l I (R := R) nx).Models ZF)
    {U₀ ω κ L F β X K j δ T ca cb Y₁ T₁ κ' U E u U' E' u' τ Dw w b z pp pb ph α W q n m :
      (smdl_structure_l I (R := R) nx).Domain}
    {σ : Fin 7 → (smdl_structure_l I (R := R) nx).Domain}
    (cert : Er_rank_cut_at_d hZF Ω c₀ X₀ R₀ c Y S q₀ Γ k₀ N R z₀ cN nx (ZF.modelsKP native)
      U₀ ω κ L F β X K j Ls Js Os Zs As ps Ts Vs rs ct P Rp jt qt p₀)
    (rankX : V_d (kp_pair_l (ZF.modelsKP native)) δ X)
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP native)) ω κ K X T)
    (height : (smdl_structure_l I (R := R) nx).IsLimitOrdinal δ)
    (loc : It_local_d (kp_pair_l (ZF.modelsKP native)) ω X T κ L F)
    (mx : Smem_d (kp_pair_l (ZF.modelsKP native)) ca X T)
    (my : Smem_d (kp_pair_l (ZF.modelsKP native)) cb Y₁ T₁)
    (ultra : It_ultra_d (kp_pair_l (ZF.modelsKP native)) ω κ L F ca cb j)
    (critical : Wd_crit_d (kp_pair_l (ZF.modelsKP native)) X j κ κ')
    (κlimit : (smdl_structure_l I (R := R) nx).IsLimitOrdinal κ')
    (iU : Rd_entry_d U U' j) (iE : Rd_entry_d E E' j) (iu : Rd_entry_d u u' j)
    (reply : Td_reply_d (kp_pair_l (ZF.modelsKP native)) ω q n m κ' τ U' E' Dw u' w b z pp pb ph σ)
    (rank : V_d (kp_pair_l (ZF.modelsKP native)) α β)
    (limit : (smdl_structure_l I (R := R) nx).IsLimitOrdinal α)
    (below : (smdl_structure_l I (R := R) nx).mem α δ)
    (hU : (smdl_structure_l I (R := R) nx).mem U β)
    (hE : (smdl_structure_l I (R := R) nx).mem E β)
    (hu : (smdl_structure_l I (R := R) nx).mem u β)
    (rankW : V_d (kp_pair_l (ZF.modelsKP native)) L W)
    (hDwW : (smdl_structure_l I (R := R) nx).mem Dw W)
    (hq : (smdl_structure_l I (R := R) nx).mem q ω)
    (hm : (smdl_structure_l I (R := R) nx).mem m ω)
    (hb : (smdl_structure_l I (R := R) nx).mem b ω)
    (hz : (smdl_structure_l I (R := R) nx).mem z ω)
    (hσ : ∀ i, (smdl_structure_l I (R := R) nx).mem (σ i) ω) :
    ∃ mt : Smdl_d I ct P Rp,
      Zc_model_d I Ω ct P Rp ∧ Smap_d I Ω c ct Y P jt ∧ Smap_d I Ω c₀ ct X₀ P qt ∧
      (∀ x E, Rd_entry_d x E qt ↔ M.mem x X₀ ∧ ∃ y, Rd_entry_d x y q₀ ∧ Rd_entry_d y E jt) ∧
      It_payload_d p₀ κ.val L.val F.val ∧ It_active_d hZF Ω cN c ct jt p₀ ∧
    ∃ l V Δ g, Ic_common_d I N R P Rp L.val l W.val V Δ g ∧
      Fs_read_d (M := smdl_structure_l I (R := R) nx) ω W ∧ Rr_small_d I N R W.val ∧
    ∃ Kκ : (smdl_structure_l I (R := R) nx).Domain,
      V_d (kp_pair_l (ZF.modelsKP native)) κ Kκ ∧
      (∀ x : (smdl_structure_l I (R := R) nx).Domain, ∀ a E,
        (smdl_structure_l I (R := R) nx).mem x Kκ → Rd_entry_d x.val a k₀ →
          (Rd_entry_d x.val E g ↔ Rd_entry_d a E jt)) ∧
    ∃ A₁ Q₁ B₁ e₁ : (smdl_structure_l I (R := R) nx).Domain, ∃ Dp t H,
      Eb_collapse_d ω κ L K X β F A₁ Q₁ B₁ e₁ ∧
      (smdl_structure_l I (R := R) nx).TransitiveSet B₁ ∧
      (∀ x, M.mem x Dp ↔ M.mem x N ∧ Rd_entry_d x B₁.val R) ∧
      M.IsSetInjectionFromTo I t Dp P ∧ M.IsRestrictionOf I g t Δ ∧
      Rd_entry_d L.val l t ∧ Rd_entry_d W.val V t ∧ M.mem H P ∧
      (∀ E, Rd_entry_d E H Rp ↔ ∃ x, M.mem x Dp ∧ Rd_entry_d x E t) ∧
      (∀ x E, Rd_entry_d x E t → ∀ y, Rd_entry_d y E Rp ↔
        ∃ a, Rd_entry_d a x R ∧ Rd_entry_d a y t) ∧
      (∀ x y : (smdl_structure_l I (R := R) nx).Domain, ∀ a E,
        (smdl_structure_l I (R := R) nx).mem x β → Rd_entry_d x y j →
          Rd_entry_d x.val a k₀ → (Rd_entry_d y.val E t ↔ Rd_entry_d a E jt)) ∧
    ∃ ε : Env (smdl_structure_l I (R := Rp) mt.2.1) 23,
      (∀ i, Rd_entry_d (td_reply_values_d ω q n m κ' τ U' E' Dw u' w b z pp pb ph σ i).val
        (ε.bound i).val t) ∧ Formula.satisfies ε td_reply0_m ∧
      (∃ zt, Rr_layer_d I Ω P Rp (ε.bound 0).val zt) ∧
      Rd_entry_d ω.val (ε.bound 0).val g ∧
      Rd_entry_d (ε.bound 1).val (ε.bound 0).val Rp ∧
      Rd_entry_d (ε.bound 2).val (ε.bound 0).val Rp ∧
      Rd_entry_d (ε.bound 3).val (ε.bound 0).val Rp ∧
      (∀ x, Rd_entry_d x l Rp → Rd_entry_d x (ε.bound 4).val Rp) := by
  let Nn := smdl_structure_l I (R := R) nx
  have hN := ZF.modelsKP native
  -- 后继、共同层和完整池均由这一次原施加证书选定。
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,mt,_,_,_,embed,rootMap,_,_,payload,active,certificate,rootGraph,
    Uc,rankUc,readW,_,small,l,V,Δ,g,common,_,_,Kκ,rankKκ,lowSquare,
    _,bκ,κt,_,ibκ,iκt,_,boundκ,_,_,_,_,_,_,_,_,rest⟩ := cert
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,rest⟩ := rest
  obtain ⟨_,wT,_,zt,_,iwT,_,_,numbers,_,_,_,_,_,_,_,_,_,_,_,pool,_⟩ := rest
  obtain ⟨A₁,Q₁,B₁,e₁,_,Dp,_,_,t,owned,_,carrier,_,_,_,_,ft,restrict,endpoint,layer,_,_,
    _,H,_,iH,full,pred,commute,_⟩ := pool
  have eqW := ZF.v_unique_l (kp_pair_l hN) native rankUc rankW
  subst Uc
  have target := certificate root
  have targetZF := ZFC.models_zf_l (target.native_l I hZF hΩ)
  have hP := ZF.modelsKP targetZF
  have hH := embed.1.1.output_mem_of_pairMember iH
  -- Dw 属于实际 V_L；池图保存 V_L 的点，故所属证明直接进入同一个 B₁。
  have hWB : Nn.mem W B₁ := ((carrier W.val).mp (ft.1.input_mem_of_pairMember layer)).2
  have data := owned
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,collapse,_⟩ := data
  have hDwB : Nn.mem Dw B₁ := collapse.transitive W hWB Dw hDwW
  obtain ⟨transB,pairB,nb,ρ,values,truth⟩ := td_reply_pool_l native rankX source height loc mx my ultra
    critical κlimit iU iE iu reply rank limit below hU hE hu owned hDwB hq hb hz hσ
  let Hn : (smdl_structure_l I (R := Rp) mt.2.1).Domain := ⟨H,hH⟩
  obtain ⟨ε,points,valid⟩ := td_reply_raw_image_l I nx mt.2.1 hP B₁ Hn pairB nb ρ truth carrier ft full pred
  have actual i : Rd_entry_d (td_reply_values_d ω q n m κ' τ U' E' Dw u' w b z pp pb ph σ i).val
      (ε.bound i).val t :=
    Eq.mp (congrArg (fun x : Nn.Domain => Rd_entry_d x.val (ε.bound i).val t) (values i)) (points i)
  have eqω := ft.1.1.2 ω.val wT (ε.bound 0).val ((restrict.2 _ _).mp iwT).2 (actual 0)
  have nums : Rr_layer_d I Ω P Rp (ε.bound 0).val zt := eqω ▸ numbers
  have omega : Rd_entry_d ω.val (ε.bound 0).val g := eqω ▸ iwT
  -- n 由同一 dcp 的实际后继关系得到；m 使用完整回答类型自己的有限元数。
  have data := reply
  obtain ⟨_,v,drop,⟨_,_,code,query,_⟩,_⟩ := data
  obtain ⟨n₀,sn,hn₀⟩ := source.omega.1.2 q hq
  have hn : Nn.mem n ω := sn.eq native.1 drop.1 ▸ hn₀
  have finite (i : Fin 23)
      (hi : Nn.mem (td_reply_values_d ω q n m κ' τ U' E' Dw u' w b z pp pb ph σ i) ω) :
      Rd_entry_d (ε.bound i).val (ε.bound 0).val Rp := by
    apply (pred _ _ (points 0) _).mpr
    refine ⟨_,?_,points i⟩
    rw [values i,values 0]
    exact hi
  -- 回答的实际常量域已含 κ′；沿同一次超幂回拉便得到 κ∈β。
  -- 常值方块因此把第 4 槽识别为同一原边的临界像，保存共同层端点界。
  have pj := ultra.elementary_l native mx.1 my.1
  have hκU : Nn.mem κ U :=
    (pj.member_l (kp_pair_l hN) native source.omega mx my critical.image iU).mpr
      query.constants.2.2.2.2.1
  have hκβ := (v_transitive_l (kp_pair_l hN) rank) U hU κ hκU
  have criticalPoint := (commute κ κ' bκ (ε.bound 4).val hκβ critical.image ibκ).mp (actual 4)
  have eqκ := embed.1.1.1.2 bκ κt (ε.bound 4).val iκt criticalPoint
  have cap x (hx : Rd_entry_d x l Rp) : Rd_entry_d x (ε.bound 4).val Rp :=
    eqκ ▸ boundκ x hx
  refine ⟨mt,target,embed,rootMap,rootGraph,payload,active,l,V,Δ,g,common,readW,small,
    Kκ,rankKκ,lowSquare,A₁,Q₁,B₁,e₁,Dp,t,H,owned,transB,carrier,ft,restrict,endpoint,layer,hH,
    full,pred,commute,ε,actual,valid,⟨zt,nums⟩,omega,finite 1 hq,finite 2 hn,finite 3 hm,cap⟩

end YesMetaZFC.SetTheory.LargeCardinal
