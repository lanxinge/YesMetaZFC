import YesMetaZFC.Model.SetTheory.Relations.LayerComposition
import YesMetaZFC.SetTheory.LargeCardinal.Game.NativePlay
import YesMetaZFC.SetTheory.LargeCardinal.Game.Subtype
import YesMetaZFC.Model.SetTheory.Relations.CollectCode
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CopyAnchor
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.FrameUnion

/-! # 原请求确定背景中的完整有限对局前缀

前缀的定义域和值域分别沿数字图和真实根图解释，事件仍在当前原关系的
反射层中核验。所有内部有限坐标一起回读，不要求字母或自然数对象码字面固定。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

def Tg_prefix_d (k A X R C c b h z p f : M.Domain) : Prop :=
  Fn0_d k A f ∧ ∃ s, Tg_play_d I X R C c b h s ∧
    ∀ i x, M.mem i k → M.mem x A →
      (Rd_entry_d i x f ↔ ∃ n y, M.PairMember I i n z ∧ M.PairMember I x y p ∧ Rf_val_d I X R n y s)

variable (hZF : M.Models ZF)
local notation "K" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_context_d.prefix_l {X R w η C Ω z k p A B t : M.Domain}
    (context : Tg_context_d K w X R η C) (nx : ∃ x, M.mem x X)
    (ext : Extensional (smdl_structure_l K (R := R) nx))
    (nc : Nonempty {x : (smdl_structure_l K (R := R) nx).Domain //
      (smdl_structure_l K (R := R) nx).mem x ⟨C,context.member⟩})
    (θ : Env (rt_model_l (M := smdl_structure_l K (R := R) nx) ⟨C,context.member⟩ nc) 46)
    (issued : Formula.satisfies θ tg_issued0_m) (numbers : Rr_layer_d K Ω X R w z)
    (point : Rd_entry_d k (θ.bound 19).val.val z)
    (carrier : ∀ y, M.mem y B ↔ M.mem y X ∧ Rd_entry_d y (θ.bound 6).val.val R)
    (letters : M.IsSetBijectionFromTo K t A B) (rest : M.IsRestrictionOf K t p A) :
    ∃ f, Tg_prefix_d K k A X R C (θ.bound 4).val.val (θ.bound 3).val.val (θ.bound 20).val.val z p f := by
  have fs := context.finite_l nx ext
  let J := rt_pair_l fs.transitive nc ext fs.pair
  have ep := rt_model_ext_l ext fs.transitive nc
  obtain ⟨h,s,_,_,_,_,_,_,_,_,_,endh,digits,_⟩ := tg_issued_query_l J ep θ issued
  have play : Tg_play_d K X R C (θ.bound 4).val.val (θ.bound 3).val.val (θ.bound 20).val.val s.val.val :=
    (tg_play_native_l K nx ext ⟨C,context.member⟩ fs.transitive nc J
      (θ.bound 4) (θ.bound 3) (θ.bound 20) s).mpr
      (fun i x hi => ((digits.2 i x (digits.1.bound_l hi).1).mp hi).end_l endh)
  have fn := (rt_fn_l fs.transitive nc ext (θ.bound 19) (θ.bound 6) s).mp digits.1
  obtain ⟨f,ff,graph⟩ := numbers.function_pull_alphabet_l hZF ext
    (θ.bound 19).val (θ.bound 6).val s.val point fn carrier letters
  refine ⟨f,ff,s.val.val,play,?_⟩
  intro i x hi hx
  constructor
  · intro hix
    obtain ⟨n,_,hin⟩ := numbers.injection.1.2.2 i
      (numbers.transitive k (numbers.injection.1.input_mem_of_pairMember point) i hi)
    obtain ⟨y,_,hxy⟩ := letters.1.1.2.2 x hx
    exact ⟨n,y,hin,((rest.2 x y).mp hxy).2,(graph i n x y hin hxy).mp hix⟩
  · rintro ⟨n,y,hin,hxy,val⟩
    exact (graph i n x y hin ((rest.2 x y).mpr ⟨hx,hxy⟩)).mpr val

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 同一背景原前缀跨实际原树边保持

原函数码和历史沿同一个初等图搬运，数字坐标沿两份完整解释交换，
字母坐标沿根图复合交换。背景前缀函数本身保持不变。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_prefix_d.map_l {Ω c X R d Y S j w w' z z' q q' C C' a a' b b' h h' k A f : M.Domain}
    (hΩ : M.IsOmega Ω) (mx : Smdl_d I c X R) (my : Smdl_d I d Y S)
    (map : Smap_d I Ω c d X Y j) (ext : Rf_ext_d I X R) (ext' : Rf_ext_d I Y S)
    (source : Rr_layer_d I Ω X R w z) (target : Rr_layer_d I Ω Y S w' z')
    (letters : ∀ x, M.mem x A → ∃ y, M.mem y X ∧ M.PairMember I x y q)
    (hk : M.MemberSubset k Ω)
    (function : M.IsSetFunction I q')
    (comp : ∀ x y t, M.PairMember I x y q → M.PairMember I y t j → M.PairMember I x t q')
    (iC : M.PairMember I C C' j) (ia : M.PairMember I a a' j)
    (ib : M.PairMember I b b' j) (ih : M.PairMember I h h' j)
    (prior : Tg_prefix_d I k A X R C a b h z q f) :
    Tg_prefix_d I k A Y S C' a' b' h' z' q' f := by
  obtain ⟨fn,s,play,graph⟩ := prior
  obtain ⟨s',_,iss⟩ := map.1.1.2.2 s (play.elim fun members _ => members 4)
  have next := play.map_l I hZF hΩ mx my map iC ia ib ih iss
  have numbers := (source.omega_map_l I hZF hΩ mx my map ext ext' target).2
  refine ⟨fn,s',next,?_⟩
  intro i x hi hx
  constructor
  · intro value
    obtain ⟨n,y,hin,hxy,val⟩ := (graph i x hi hx).mp value
    obtain ⟨n',_,hin'⟩ := target.injection.1.2.2 i (hk i hi)
    obtain ⟨y',_,iyy⟩ := map.1.1.2.2 y (val.bounds_l I).2.1
    exact ⟨n',y',hin',comp x y y' hxy iyy,
      val.map_l I hZF hΩ mx my map (numbers i n n' hin hin') iyy iss⟩
  · rintro ⟨n',y',hin',hxy',val⟩
    obtain ⟨n,_,hin⟩ := source.injection.1.2.2 i (hk i hi)
    obtain ⟨y,hy,hxy⟩ := letters x hx
    obtain ⟨v,_,iyv⟩ := map.1.1.2.2 y hy
    have same := function.2 x v y' (comp x y v hxy iyv) hxy'
    have iyy : M.PairMember I y y' j := same ▸ iyv
    exact (graph i x hi hx).mpr ⟨n,y,hin,hxy,
      val.pull_l I hZF hΩ mx my map (numbers i n n' hin hin') iyy iss⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原对局前缀的一阶编码

有限背景函数的每个值沿同一数字图及原根图，精确对应原关系中的实际
控制事件。原迭代及工作复制状态共同使用此编码，不附加工作历史。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def tg_prefix_m {d} (k A X R C c b h z p f : Term d) : Formula 1 d := set[d] ⟪
  ⌜fn0_m⌝ₚ(⌜k⌝ₛ,⌜A⌝ₛ,⌜f⌝ₛ) ∧ (∃ s, ⌜tg_play_m⌝ₚ(⌜X⌝ₛ,⌜R⌝ₛ,⌜C⌝ₛ,⌜c⌝ₛ,⌜b⌝ₛ,⌜h⌝ₛ,s) ∧
  (∀ i x, i ∈ ⌜k⌝ₛ → x ∈ ⌜A⌝ₛ → (⌜rd_entry0_m⌝ₚ(i,x,⌜f⌝ₛ) ↔ (∃ n y,
    ⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(i,n,⌜z⌝ₛ) ∧
    ⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(x,y,⌜p⌝ₛ) ∧
    ⌜rf_val_m (𝒞 := kpair_convention_l)⌝ₚ(⌜X⌝ₛ,⌜R⌝ₛ,n,y,s)))))⟫
derive_free_closed tg_prefix_m

theorem tg_prefix_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M)
    {d} (ρ : Env M d) (k A X R C c b h z p f : Term d) :
    Formula.satisfies ρ (tg_prefix_m k A X R C c b h z p f) ↔
      Tg_prefix_d I (k.eval ρ) (A.eval ρ) (X.eval ρ) (R.eval ρ) (C.eval ρ) (c.eval ρ)
        (b.eval ρ) (h.eval ρ) (z.eval ρ) (p.eval ρ) (f.eval ρ) := by
  simp only [tg_prefix_m,Tg_prefix_d,Formula.satisfies_conj_iff,fn0_sat_l hE,
    Formula.satisfies_exists_iff,tg_play_sat_l I,Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff,Formula.satisfies_mem_iff,Formula.satisfies_iff_iff,
    rd_entry0_sat_l hE,Formula.satisfies_orderedPairMem_iff I,rf_val_sat_l I,
    Definitional.Term.eval_weaken]; rfl

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原根中的实际秩切片及完整关系解释

根切片的成员载体由原关系分离取得，绝不把原生 Vγ 当作背景 Vγ。
当前切片只逐点遵循实际根图；高度端点以全部前驱实现，故不要求根图
搬运 γ 或 Vγ 本身。初始实例使用同一根恒等图的真实限制。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

structure Tg_root_cut_d (I : kpair_convention_l.Interpretation M)
    (c X R w γ B a D A : M.Domain) : Prop where
  model : Smdl_d I c X R
  rank : Rr_rank_d I X R γ B
  limit : Rr_truth_d I X R (Formula.isLimitOrdinal .newest) (fun _ : Fin 1 => γ)
  omega : Rd_entry_d w B R
  alphabet : Rd_entry_d a B R
  carrier : ∀ x, M.mem x D ↔ M.mem x X ∧ Rd_entry_d x B R
  letters : ∀ x, M.mem x A ↔ M.mem x X ∧ Rd_entry_d x a R

structure Tg_root_slice_d (I : kpair_convention_l.Interpretation M)
    (X₀ R₀ γ₀ D₀ C₀ X R C q γ V t : M.Domain) : Prop where
  context : Rd_entry_d C₀ C q
  rank : Rr_rank_d I X R γ V
  limit : Rr_truth_d I X R (Formula.isLimitOrdinal .newest) (fun _ : Fin 1 => γ)
  injection : M.IsSetInjectionFromTo I t D₀ X
  image : ∀ y, Rd_entry_d y V R ↔ ∃ x, M.mem x D₀ ∧ Rd_entry_d x y t
  predecessors : ∀ x y, Rd_entry_d x y t → ∀ z,
    Rd_entry_d z y R ↔ ∃ a, Rd_entry_d a x R₀ ∧ Rd_entry_d a z t
  endpoint : Er_rep_d X₀ R₀ X R t γ₀ γ
  root : ∀ x y, Rd_entry_d x y t → Rd_entry_d x y q

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 根内已有的秩对象实际生成成员载体，字母载体保留原初始化给出的那一份。 -/
theorem tg_root_cut_l {c X R w γ B a A : M.Domain}
    (model : Smdl_d I c X R) (rank : Rr_rank_d I X R γ B)
    (limit : Rr_truth_d I X R (Formula.isLimitOrdinal .newest) (fun _ : Fin 1 => γ))
    (omega : Rd_entry_d w B R) (alphabet : Rd_entry_d a B R)
    (letters : ∀ x, M.mem x A ↔ M.mem x X ∧ Rd_entry_d x a R) :
    ∃ D, Tg_root_cut_d I c X R w γ B a D A := by
  let φ : UnarySchema 2 := { body := rd_entry0_m .newest (.bound 1) (.bound 2) }
  obtain ⟨D,ds⟩ := ZF.separation_exists_d hZF φ ⟨Fin.cases B (fun _ => R),fun _ => X⟩ X
  exact ⟨D,model,rank,limit,omega,alphabet,
    fun x => (ds x).trans (and_congr_right fun _ => rd_entry0_sat_l hZF.1 ..),letters⟩

/-- 原切片的向下闭包只读取给定秩证书及原生 KP。 -/
theorem Tg_root_cut_d.down_l {c X R w γ B a D A : M.Domain}
    (cut : Tg_root_cut_d I c X R w γ B a D A)
    (hN : (smdl_structure_l I (R := R) cut.model.2.1).Models KP) :
    ∀ x y, M.mem x D → Rd_entry_d y x R → M.mem y D := by
  let N := smdl_structure_l I (R := R) cut.model.2.1
  let V : N.Domain := ⟨B,cut.rank.2.1⟩
  have rank := (rr_rank_native_l I cut.model.2.1 hN ⟨γ,cut.rank.1⟩ V).mp cut.rank
  intro x y hx hy
  have xx := (cut.carrier x).mp hx
  have yy := (cut.model.2.2.2 y x hy).1
  exact (cut.carrier y).mpr ⟨yy,(v_transitive_l (kp_pair_l hN) rank) ⟨x,xx.1⟩ xx.2 ⟨y,yy⟩ hy⟩

/-- 同一个根恒等图的限制给出首切片；端点由成员实现而非 γ 的图像定义。 -/
theorem Tg_root_cut_d.identity_l {c X R w γ B a D A C q : M.Domain}
    (cut : Tg_root_cut_d I c X R w γ B a D A)
    (hN : (smdl_structure_l I (R := R) cut.model.2.1).Models KP)
    (function : M.IsSetFunction I q) (fixed : ∀ x, M.mem x X → Rd_entry_d x x q)
    (member : M.mem C X) : ∃ t, Tg_root_slice_d I X R γ D C X R C q γ B t := by
  obtain ⟨t,rest⟩ := ZF.exists_restriction hZF I q D
  have graph x y : Rd_entry_d x y t ↔ M.mem x D ∧ y = x := (rest.2 x y).trans
    ⟨fun ⟨hx,hxy⟩ => ⟨hx,function.2 x y x hxy (fixed x ((cut.carrier x).mp hx).1)⟩,
      fun ⟨hx,eq⟩ => ⟨hx,eq.symm ▸ fixed x ((cut.carrier x).mp hx).1⟩⟩
  have fn : M.IsSetFunctionFromTo I t D X :=
    ⟨rest.isSetFunction function,fun x => ⟨fun hx => ⟨x,(graph x x).mpr ⟨hx,rfl⟩⟩,
      fun ⟨y,hxy⟩ => ((graph x y).mp hxy).1⟩,
      fun x hx => ⟨x,((cut.carrier x).mp hx).1,(graph x x).mpr ⟨hx,rfl⟩⟩⟩
  have down := cut.down_l hZF hN
  refine ⟨t,fixed C member,cut.rank,cut.limit,⟨fn,?_⟩,?_,?_,?_,fun x y hxy => ((rest.2 x y).mp hxy).2⟩
  · intro x y z hx hy
    exact ((graph x z).mp hx).2.symm.trans ((graph y z).mp hy).2
  · intro y
    constructor
    · intro hy
      have hd := (cut.carrier y).mpr ⟨(cut.model.2.2.2 y B hy).1,hy⟩
      exact ⟨y,hd,(graph y y).mpr ⟨hd,rfl⟩⟩
    · rintro ⟨x,hx,hxy⟩
      exact ((graph x y).mp hxy).2.symm ▸ ((cut.carrier x).mp hx).2
  · intro x y hxy z
    obtain ⟨hx,eq⟩ := (graph x y).mp hxy
    subst y
    exact ⟨fun hz => ⟨z,hz,(graph z z).mpr ⟨down x z hx hz,rfl⟩⟩,
      fun ⟨a,ha,haz⟩ => ((graph a z).mp haz).2.symm ▸ ha⟩
  · let N := smdl_structure_l I (R := R) cut.model.2.1
    let γ₀ : N.Domain := ⟨γ,cut.rank.1⟩
    let B₀ : N.Domain := ⟨B,cut.rank.2.1⟩
    have rank := (rr_rank_native_l I cut.model.2.1 hN γ₀ B₀).mp cut.rank
    refine ⟨cut.rank.1,cut.rank.1,fun y => ⟨?_,?_⟩⟩
    · intro hy
      have yy := (cut.model.2.2.2 y γ hy).1
      have hD := (cut.carrier y).mpr ⟨yy,KP.v_ordinal_subset_l hN rank ⟨y,yy⟩ hy⟩
      exact ⟨y,yy,hy,(graph y y).mpr ⟨hD,rfl⟩⟩
    · rintro ⟨x,_,hx,hxy⟩
      exact ((graph x y).mp hxy).2.symm ▸ hx

/-- 完整关系切片把同一根图限制为原字母载体到当前原生字母的实际双射。 -/
theorem Tg_root_cut_d.alphabet_l {c X₀ R₀ w₀ γ₀ B₀ a D A C₀ X R C q γ V t b : M.Domain}
    (cut : Tg_root_cut_d I c X₀ R₀ w₀ γ₀ B₀ a D A)
    (hN : (smdl_structure_l I (R := R₀) cut.model.2.1).Models KP)
    (slice : Tg_root_slice_d I X₀ R₀ γ₀ D C₀ X R C q γ V t)
    (function : M.IsSetFunction I q) (image : Rd_entry_d a b q) :
    ∃ E f, (∀ y, M.mem y E ↔ M.mem y X ∧ Rd_entry_d y b R) ∧
      M.IsSetBijectionFromTo I f A E ∧ M.IsRestrictionOf I f q A := by
  have ha := (cut.carrier a).mpr ⟨(cut.model.2.2.2 a B₀ cut.alphabet).1,cut.alphabet⟩
  obtain ⟨b',_,hab⟩ := slice.injection.1.2.2 a ha
  have eq := function.2 a b' b (slice.root a b' hab) image
  subst b'
  have low x (hx : M.mem x A) := cut.down_l hZF hN a x ha ((cut.letters x).mp hx).2
  have graph x y (hx : M.mem x A) : Rd_entry_d x y q ↔ Rd_entry_d x y t := by
    constructor
    · intro hxy
      obtain ⟨y',_,hxy'⟩ := slice.injection.1.2.2 x (low x hx)
      exact function.2 x y' y (slice.root x y' hxy') hxy ▸ hxy'
    · exact slice.root x y
  let φ : UnarySchema 2 := { body := rd_entry0_m .newest (.bound 1) (.bound 2) }
  obtain ⟨E,es⟩ := ZF.separation_exists_d hZF φ ⟨Fin.cases b (fun _ => R),fun _ => X⟩ X
  have carrier y : M.mem y E ↔ M.mem y X ∧ Rd_entry_d y b R :=
    (es y).trans (and_congr_right fun _ => rd_entry0_sat_l hZF.1 ..)
  obtain ⟨f,rest⟩ := ZF.exists_restriction hZF I q A
  have restrict : M.IsRestrictionOf I f t A :=
    ⟨rest.1,fun x y => (rest.2 x y).trans (and_congr_right fun hx => graph x y hx)⟩
  have fn := restrict.isSetFunctionFromTo slice.injection.1 low
  have target x y (hxy : Rd_entry_d x y f) : M.mem y E := by
    obtain ⟨hx,hxy⟩ := (restrict.2 x y).mp hxy
    exact (carrier y).mpr ⟨fn.output_mem_of_pairMember ((restrict.2 x y).mpr ⟨hx,hxy⟩),
      (slice.predecessors a b hab y).mpr ⟨x,((cut.letters x).mp hx).2,hxy⟩⟩
  have ff := fn0_function_l (ZF.modelsKP hZF) ((fn0_of_function_l (ZF.modelsKP hZF) fn).retarget_l target)
  refine ⟨E,f,carrier,⟨⟨ff,?_⟩,?_⟩,rest⟩
  · intro x y z hx hy
    exact slice.injection.2 x y z ((restrict.2 x z).mp hx).2 ((restrict.2 y z).mp hy).2
  · intro y hy
    obtain ⟨x,hxa,hxy⟩ := (slice.predecessors a b hab y).mp ((carrier y).mp hy).2
    have hx := (cut.letters x).mpr ⟨((cut.carrier x).mp (slice.injection.1.input_mem_of_pairMember hxy)).1,hxa⟩
    exact ⟨x,hx,(rest.2 x y).mpr ⟨hx,slice.root x y hxy⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原根关系中的统一临界点下界

γ₀ 是根模型中的对象，不是背景序数。每个实际扩展器保存其所属节点的
完整根切片及原生 γ≤κ；根图、完整前驱与端点一并保留。恒等延伸不产生
操作，活动延伸只用本次真实 payload 的单值性加入新证书。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

def Tg_raw_critical_d (X₀ R₀ γ₀ D₀ C₀ o Q G E : M.Domain) : Prop :=
  ∀ i p κ L F, Rd_entry_d i p E → It_payload_d p κ L F →
    ∃ c X R C q γ V t, Rd_entry_d i c Q ∧ Smdl_d I c X R ∧ It_map_d G o i q ∧
      Tg_root_slice_d I X₀ R₀ γ₀ D₀ C₀ X R C q γ V t ∧
      ∀ x, Rd_entry_d x γ R → Rd_entry_d x κ R

theorem Tg_raw_critical_d.empty_l {X₀ R₀ γ₀ D₀ C₀ o Q G E : M.Domain}
    (empty : ∀ x, ¬ M.mem x E) : Tg_raw_critical_d I X₀ R₀ γ₀ D₀ C₀ o Q G E := by
  rintro i p κ L F ⟨a,_,ha⟩ _
  exact (empty a ha).elim

/-- 同一非空操作及其所属切片进入原列；旧证书沿原节点和原根边保持。 -/
theorem It_extension_d.raw_critical_apply_l (hKP : M.Models KP)
    {X₀ R₀ γ₀ D₀ C₀ o α ξ k T Q G E β T' Q' G' E' p κ L F c X R C q γ V t : M.Domain}
    (extension : It_extension_d α ξ k T Q G E β T' Q' G' E')
    (domain : ∀ i c, Rd_entry_d i c Q → M.mem i α)
    (old : Tg_raw_critical_d I X₀ R₀ γ₀ D₀ C₀ o Q G E)
    (function : M.IsSetFunction (kp_pair_l hKP) E') (entry : Rd_entry_d ξ p E')
    (payload : It_payload_d p κ L F) (node : Rd_entry_d ξ c Q') (model : Smdl_d I c X R)
    (origin : It_map_d G' o ξ q)
    (slice : Tg_root_slice_d I X₀ R₀ γ₀ D₀ C₀ X R C q γ V t)
    (lower : ∀ x, Rd_entry_d x γ R → Rd_entry_d x κ R) :
    Tg_raw_critical_d I X₀ R₀ γ₀ D₀ C₀ o Q' G' E' := by
  classical
  intro i a μ ν H event pay
  by_cases eq : i = ξ
  · subst i
    have eq := function.2 ξ a p event entry
    subst a
    have same := (payload.unique_l pay).1
    exact ⟨c,X,R,C,q,γ,V,t,node,model,origin,slice,same ▸ lower⟩
  · obtain ⟨c,X,R,C,q,γ,V,t,node,model,origin,slice,lower⟩ :=
      old i a μ ν H ((extension.2.2.2.2.2 i a eq).mp event) pay
    exact ⟨c,X,R,C,q,γ,V,t,extension.2.2.1 i c node,model,
      (extension.2.2.2.1 o i q (domain i c node)).mpr origin,slice,lower⟩

/-- 实际恒等操作没有扩展器 payload，故只保持已有原根下界。 -/
theorem It_extension_d.raw_critical_pad_l
    {X₀ R₀ γ₀ D₀ C₀ o α ξ k T Q G E β T' Q' G' E' : M.Domain}
    (extension : It_extension_d α ξ k T Q G E β T' Q' G' E')
    (domain : ∀ i c, Rd_entry_d i c Q → M.mem i α)
    (old : Tg_raw_critical_d I X₀ R₀ γ₀ D₀ C₀ o Q G E)
    (empty : ∀ p, Rd_entry_d ξ p E' → ∀ x, ¬ M.mem x p) :
    Tg_raw_critical_d I X₀ R₀ γ₀ D₀ C₀ o Q' G' E' := by
  classical
  intro i p κ L F event pay
  by_cases eq : i = ξ
  · subst i
    obtain ⟨r,⟨a,b,_,_,pair⟩,_⟩ := pay
    exact (empty p event a ((pair a).mpr (Or.inl rfl))).elim
  · obtain ⟨c,X,R,C,q,γ,V,t,node,model,origin,slice,lower⟩ :=
      old i p κ L F ((extension.2.2.2.2.2 i p eq).mp event) pay
    exact ⟨c,X,R,C,q,γ,V,t,extension.2.2.1 i c node,model,
      (extension.2.2.2.1 o i q (domain i c node)).mpr origin,slice,lower⟩

end YesMetaZFC.SetTheory.LargeCardinal
