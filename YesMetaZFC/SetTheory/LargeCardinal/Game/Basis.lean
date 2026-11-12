import YesMetaZFC.SetTheory.LargeCardinal.Iteration.FrameUnion
import YesMetaZFC.Model.SetTheory.Relations.Parity
import YesMetaZFC.Model.SetTheory.Relations.RankImage
import YesMetaZFC.Model.SetTheory.Embedding.Relative
import YesMetaZFC.Model.SetTheory.Relations.SliceEmbedding

/-! # 原秩层在实际根图上的完整解释

序数和秩层分别由完整前驱图解释，秩在当前原关系中判断。根图只须与
秩层成员的解释一致；层号和整个秩层的对象码不要求被根图固定。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Tg_anchor_d (I : kpair_convention_l.Interpretation M) (γ B X R π : M.Domain) : Prop :=
  ∃ a V s t, Rr_layer_d I γ X R a s ∧ Rr_layer_d I B X R V t ∧ Rr_rank_d I X R a V ∧
    ∀ x y, Rd_entry_d x y t → Rd_entry_d x y π

def tg_anchor_m {d} (γ B X R π : Term d) : Formula 1 d := set[d] ⟪∃ a V s t,
  ⌜rr_layer_m⌝ₚ(⌜γ⌝ₛ, ⌜X⌝ₛ, ⌜R⌝ₛ, a, s) ∧ ⌜rr_layer_m⌝ₚ(⌜B⌝ₛ, ⌜X⌝ₛ, ⌜R⌝ₛ, V, t) ∧
  ⌜rr_rank_m⌝ₚ(⌜X⌝ₛ, ⌜R⌝ₛ, a, V) ∧ (∀ x y, ⌜rd_entry0_m⌝ₚ(x, y, t) → ⌜rd_entry0_m⌝ₚ(x, y, ⌜π⌝ₛ))⟫
derive_free_closed tg_anchor_m

theorem tg_anchor_sat_l (I : kpair_convention_l.Interpretation M) (ext : Extensional M)
    {d} (ρ : Env M d) (γ B X R π : Term d) :
    Formula.satisfies ρ (tg_anchor_m γ B X R π) ↔
      Tg_anchor_d I (γ.eval ρ) (B.eval ρ) (X.eval ρ) (R.eval ρ) (π.eval ρ) := by
  simp only [tg_anchor_m, Tg_anchor_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    rr_layer_sat_l I ext, rr_rank_sat_l I, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    rd_entry0_sat_l ext, Definitional.Term.eval_weaken]; rfl

/-- 真实传递隶属表示中，完整解释还原为原层及其逐点固定性。 -/
theorem Tg_anchor_d.read_l (hKP : M.Models KP) {γ B c X R π : M.Domain}
    (h : Tg_anchor_d (kp_pair_l hKP) γ B X R π) (trans : M.TransitiveSet X)
    (model : Smem_d (kp_pair_l hKP) c X R) :
    M.mem γ X ∧ M.mem B X ∧ Vr_d X γ B ∧ ∀ x, M.mem x B → Rd_entry_d x x π := by
  obtain ⟨a, V, s, t, height, layer, rank, fixed⟩ := h
  obtain ⟨ea, _⟩ := height.mem_l hKP trans model
  obtain ⟨ev, graph⟩ := layer.mem_l hKP trans model
  have hγ := ea ▸ height.member
  have hB := ev ▸ layer.member
  exact ⟨hγ, hB, (rr_rank_mem_l (kp_pair_l hKP) hKP model trans hγ hB).mp (ea ▸ ev ▸ rank),
    fun x hx => fixed x x ((graph x x).mpr ⟨hx, rfl⟩)⟩

section Transport
variable (hKP : M.Models KP)
local notation "I" => kp_pair_l hKP

/-- 同一原低层在两侧的完整解释沿实际复合根图交换。 -/
theorem Tg_anchor_d.extend_l {γ B Y S C W q q' j h a V r s t : M.Domain}
    (prior : Tg_anchor_d I γ B Y S q) (ext : Rf_ext_d I Y S)
    (left : Rr_layer_d I B Y S h r) (height : Rr_layer_d I γ C W a s)
    (right : Rr_layer_d I B C W V t) (rank : Rr_rank_d I C W a V)
    (step : ∀ x b, Rd_entry_d x b r → ∀ E, Rd_entry_d x E t ↔ Rd_entry_d b E j)
    (comp : It_comp_d q j q') : Tg_anchor_d I γ B C W q' := by
  obtain ⟨a₀, V₀, s₀, t₀, _, old, _, fixed⟩ := prior
  have eq := (left.unique_l hKP old ext).2
  refine ⟨a, V, s, t, height, right, rank, ?_⟩
  intro x E hxE
  obtain ⟨b, _, hxb⟩ := left.injection.1.2.2 x (right.injection.1.input_mem_of_pairMember hxE)
  exact (comp.2 x E).mpr ⟨b, fixed x b (eq ▸ hxb), (step x b hxb E).mp hxE⟩

end Transport

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 已有真实隶属实例给出完整锚点，不向一般原关系模型添加传递性。 -/
theorem Tg_anchor_d.of_mem_l {γ B c X R π : M.Domain} (model : Smem_d I c X R)
    (trans : M.TransitiveSet X) (hγ : M.mem γ X) (hB : M.mem B X) (rank : Vr_d X γ B)
    (fixed : ∀ x, M.mem x B → Rd_entry_d x x π) : Tg_anchor_d I γ B X R π := by
  obtain ⟨s, height, _⟩ := rr_layer_mem_l I hZF model trans hγ (rank.ordinal_l hB).transitive
  obtain ⟨t, layer, graph⟩ := rr_layer_mem_l I hZF model trans hB (rank.transitive_l trans hB)
  refine ⟨γ, B, s, t, height, layer, (rr_rank_mem_l I (ZF.modelsKP hZF) model trans hγ hB).mpr rank, ?_⟩
  intro x y hxy
  obtain ⟨hx, eq⟩ := (graph x y).mp hxy
  rw [← eq]
  exact fixed x hx

/-- 实际树的恒等根图同时解释原序数层及原字母表所在秩层。 -/
theorem It_diagram_d.anchor_root_l {ω α T J G i c X R β B : M.Domain}
    (tree : It_diagram_d (kp_pair_l (ZF.modelsKP hZF)) ω α T J G) (hc : Rd_entry_d i c J) (model : Smem_d I c X R)
    (ht : M.TransitiveSet X) (hβ : M.mem β X) (hB : M.mem B X) (rank : Vr_d X β B) :
    ∃ π, It_map_d G i i π ∧ (∀ x, M.mem x X → Rd_entry_d x x π) ∧ Tg_anchor_d I β B X R π := by
  obtain ⟨π, edge⟩ := tree.map_l hZF (tree.order.refl i ((tree.model_domain i).mpr ⟨c, hc⟩))
  have j := tree.elementary i i π c X R c X R edge hc hc model.1 model.1
  have fixed x (hx : M.mem x X) : Rd_entry_d x x π := by
    obtain ⟨y, _, image⟩ := j.1.1.2.2 x hx
    exact (tree.identity i π edge x y image).symm ▸ image
  exact ⟨π, edge, fixed, Tg_anchor_d.of_mem_l hZF model ht hβ hB rank (fun x hx => fixed x (ht B hB x hx))⟩

/-- 完整初等图的真实临界点严格高于 ω。 -/
theorem Wd_crit_d.omega_lt_l {ω κ κ' X Y c R d S j : M.Domain}
    (critical : Wd_crit_d I X j κ κ') (hω : M.IsOmega ω) (xt : M.TransitiveSet X) (yt : M.TransitiveSet Y)
    (mx : Smem_d I c X R) (my : Smem_d I d Y S) (embed : Smap_d I ω c d X Y j) (hw : M.mem ω X) : M.mem ω κ := by
  have omega := embed.omega_l I hZF hω xt yt mx my hw
  have natural := embed.natural_l hZF hω xt yt mx my hw
  rcases (hω.isOrdinal (ZF.modelsKP hZF)).trichotomy hZF.1 critical.ordinal (KP.difference_exists_d (ZF.modelsKP hZF))
    (KP.intersection_exists_d (ZF.modelsKP hZF) ω κ) with eq | lt | gt
  · have eq := hZF.1.eq_of_same_members ω κ eq
    exact (critical.moved (embed.1.1.1.2 κ κ κ' (eq ▸ omega) critical.image)).elim
  · exact lt
  · exact (critical.moved (embed.1.1.1.2 κ κ κ' (natural κ gt) critical.image)).elim

/-- 固定秩层中的整份有限原公式，沿同一根的两条实际图往返。 -/
theorem Tg_anchor_d.peer_l {ω β B r Z Q x X R y Y S π σ C₀ C D : M.Domain}
    (anchor : Tg_anchor_d I β B X R π) (target : Tg_anchor_d I β B Y S σ)
    (hω : M.IsOmega ω) (xt : M.TransitiveSet X) (yt : M.TransitiveSet Y)
    (mz : Smdl_d I r Z Q) (mx : Smem_d I x X R) (my : Smem_d I y Y S)
    (j : Smap_d I ω r x Z X π) (k : Smap_d I ω r y Z Y σ)
    (iC : Rd_entry_d C₀ C π) (iD : Rd_entry_d C₀ D σ) (ct : M.TransitiveSet C) (dt : M.TransitiveSet D)
    (nc : Nonempty {a // M.mem a C}) (nd : Nonempty {a // M.mem a D}) {n}
    (φ : Formula 1 n) (closed : φ.FreeClosed) (ρ : Env (rt_model_l C nc) n)
    (low : ∀ i, M.mem (ρ.bound i).val B) (valid : Formula.satisfies ρ φ) :
    ∃ θ : Env (rt_model_l D nd) n, (∀ i, (θ.bound i).val = (ρ.bound i).val) ∧ Formula.satisfies θ φ := by
  have fx := (anchor.read_l (ZF.modelsKP hZF) xt mx).2.2.2
  have fy := (target.read_l (ZF.modelsKP hZF) yt my).2.2.2
  have fixed i := fx (ρ.bound i).val (low i)
  have fixed' i := fy (ρ.bound i).val (low i)
  have root i := (j.relation_l I hZF hω mz mx.1 (fixed i) iC).mpr
    ((mx.2 (ρ.bound i).val C).mpr ⟨j.1.1.output_mem_of_pairMember (fixed i),
      j.1.1.output_mem_of_pairMember iC, (ρ.bound i).property⟩)
  have inside i := ((my.2 (ρ.bound i).val D).mp
    ((k.relation_l I hZF hω mz my.1 (fixed' i) iD).mp (root i))).2.2
  have inhabited := nd
  obtain ⟨a⟩ := inhabited
  let θ : Env (rt_model_l D nd) n := ⟨fun i => ⟨(ρ.bound i).val, inside i⟩, fun _ => a⟩
  obtain ⟨f, left, cf⟩ := rr_layer_mem_l I hZF mx xt (j.1.1.output_mem_of_pairMember iC) ct
  obtain ⟨g, right, dg⟩ := rr_layer_mem_l I hZF my yt (k.1.1.output_mem_of_pairMember iD) dt
  exact ⟨θ, fun _ => rfl, (smap_peer_l hZF hω mz mx.1 my.1 j k left right iC iD nc nd
    φ closed ρ θ (fun i => (ρ.bound i).val) (fun i => (ρ.bound i).val) (fun i => (θ.bound i).val)
    fixed fixed' (fun i => (cf _ _).mpr ⟨(ρ.bound i).property, rfl⟩)
    (fun i => (dg _ _).mpr ⟨(θ.bound i).property, rfl⟩)).mp valid⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 根锚点给出实际字母表满像

原字母表属于完整低层时，该层的前驱方程覆盖其像的全部原成员。
根图单值性把层图在字母表上的限制识别为同一个根图限制，因而得到
原字母集合到当前原生字母集合的实际双射，不要求对象码字面固定。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_anchor_d.alphabet_l {γ Bγ X R p A a : M.Domain}
    (anchor : Tg_anchor_d I γ Bγ X R p) (function : M.IsSetFunction I p)
    (hA : M.mem A Bγ) (image : Rd_entry_d A a p) :
    ∃ L t, (∀ y, M.mem y L ↔ M.mem y X ∧ Rd_entry_d y a R) ∧
      M.IsSetBijectionFromTo I t A L ∧ M.IsRestrictionOf I t p A := by
  obtain ⟨_,_,_,s,_,layer,_,fixed⟩ := anchor
  obtain ⟨a',_,hAa⟩ := layer.injection.1.2.2 A hA
  have eq := function.2 A a' a (fixed A a' hAa) image
  have hAa : Rd_entry_d A a s := eq ▸ hAa
  have graph x y (hx : M.mem x A) : Rd_entry_d x y p ↔ Rd_entry_d x y s := by
    constructor
    · intro hxy
      obtain ⟨z,_,hxz⟩ := layer.injection.1.2.2 x (layer.transitive A hA x hx)
      exact function.2 x z y (fixed x z hxz) hxy ▸ hxz
    · exact fixed x y
  let φ : UnarySchema 2 := { body := rd_entry0_m .newest (.bound 1) (.bound 2) }
  obtain ⟨L,spec⟩ := ZF.separation_exists_d hZF φ ⟨Fin.cases a (fun _ => R),fun _ => X⟩ X
  have carrier y : M.mem y L ↔ M.mem y X ∧ Rd_entry_d y a R :=
    (spec y).trans (and_congr_right fun _ => rd_entry0_sat_l hZF.1 ..)
  obtain ⟨t,rest⟩ := ZF.exists_restriction hZF I p A
  have cut : M.IsRestrictionOf I t s A :=
    ⟨rest.1,fun x y => (rest.2 x y).trans (and_congr_right fun hx => graph x y hx)⟩
  have ft : M.IsSetFunctionFromTo I t A X :=
    cut.isSetFunctionFromTo layer.injection.1 (layer.transitive A hA)
  have bound x y (hxy : Rd_entry_d x y t) : M.mem y L := by
    obtain ⟨hx,hs⟩ := (cut.2 x y).mp hxy
    exact (carrier y).mpr ⟨ft.output_mem_of_pairMember hxy,
      (layer.predecessors A a hAa y).mpr ⟨x,hx,hs⟩⟩
  have fl : M.IsSetFunctionFromTo I t A L := ⟨ft.1,ft.2.1,fun x hx =>
    (ft.2.2 x hx).imp fun y hy => ⟨bound x y hy.2,hy.2⟩⟩
  refine ⟨L,t,carrier,⟨⟨fl,?_⟩,?_⟩,rest⟩
  · intro x y z hx hy
    exact layer.injection.2 x y z ((cut.2 x z).mp hx).2 ((cut.2 y z).mp hy).2
  · intro y hy
    obtain ⟨x,hx,hxy⟩ := (layer.predecessors A a hAa y).mp ((carrier y).mp hy).2
    exact ⟨x,hx,(rest.2 x y).mpr ⟨hx,fixed x y hxy⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原关系反射层之间的固定低层公式传输

参数通过完整低层坐标图取得共同根原像。目标参数仍使用目标自己的对象码，
量词遍及整个目标反射层；低层图仅用于识别参数，不替代完整公式的传输。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_anchor_d.native_peer_l {ω γ B r Z Q x X R y Y S π σ C₀ H f : M.Domain}
    (anchor : Tg_anchor_d I γ B X R π) (target : Tg_anchor_d I γ B Y S σ)
    (hω : M.IsOmega ω) (mz : Smdl_d I r Z Q) (mx : Smdl_d I x X R) (my : Smdl_d I y Y S)
    (j : Smap_d I ω r x Z X π) (k : Smap_d I ω r y Z Y σ)
    (ext : Rf_ext_d I X R) (source : Rr_layer_d I B X R H f)
    (C : (smdl_structure_l I (R := R) mx.2.1).Domain)
    (D : (smdl_structure_l I (R := S) my.2.1).Domain)
    (ct : (smdl_structure_l I (R := R) mx.2.1).TransitiveSet C)
    (dt : (smdl_structure_l I (R := S) my.2.1).TransitiveSet D)
    (nc : Nonempty {a : (smdl_structure_l I (R := R) mx.2.1).Domain //
      (smdl_structure_l I (R := R) mx.2.1).mem a C})
    (nd : Nonempty {a : (smdl_structure_l I (R := S) my.2.1).Domain //
      (smdl_structure_l I (R := S) my.2.1).mem a D})
    (iC : Rd_entry_d C₀ C.val π) (iD : Rd_entry_d C₀ D.val σ)
    {n} (φ : Formula 1 n) (closed : φ.FreeClosed) (ρ : Env (rt_model_l C nc) n)
    (low : ∀ i, Rd_entry_d (ρ.bound i).val.val H R) (valid : Formula.satisfies ρ φ) :
    ∃ θ : Env (rt_model_l D nd) n,
      (∀ i, ∃ a, Rd_entry_d a (ρ.bound i).val.val f ∧ Rd_entry_d a (θ.bound i).val.val σ) ∧
      Formula.satisfies θ φ := by
  obtain ⟨a, U, s, t, _, layer, _, fixed⟩ := anchor
  have eq := (source.unique_l (ZF.modelsKP hZF) layer ext).2
  have lift x y (hxy : Rd_entry_d x y f) : Rd_entry_d x y π := fixed x y (eq ▸ hxy)
  obtain ⟨b, V, s', t', _, next, _, fixed'⟩ := target
  obtain ⟨v, hv⟩ := Classical.axiomOfChoice (fun i => (source.image (ρ.bound i).val.val).mp (low i))
  have points i : ∃ z : (rt_model_l D nd).Domain, Rd_entry_d (v i) z.val.val σ := by
    obtain ⟨z, hz, hz'⟩ := next.injection.1.2.2 (v i) (hv i).1
    have old := (j.relation_l I hZF hω mz mx (lift _ _ (hv i).2) iC).mpr (ρ.bound i).property
    exact ⟨⟨⟨z, hz⟩, (k.relation_l I hZF hω mz my (fixed' _ _ hz') iD).mp old⟩,
      fixed' _ _ hz'⟩
  obtain ⟨v', hv'⟩ := Classical.axiomOfChoice points
  have inhabited := nd
  obtain ⟨d⟩ := inhabited
  let θ : Env (rt_model_l D nd) n := ⟨v', fun _ => d⟩
  exact ⟨θ, fun i => ⟨v i, (hv i).2, hv' i⟩,
    (smap_slice_peer_l hZF hω mz mx my j k C D ct dt nc nd iC iD φ closed ρ θ v
      (fun i => lift _ _ (hv i).2) hv').mp valid⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 初值、运行状态和原档案共用的固定根基底

基底保留根反射层的实际像、γ 与 Vγ 的完整解释、原生极限性及 ω 所属。
它不依赖尚未产生的回答存档；读取低层锚点时只使用其中相应的较弱事实。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

def Tg_basis_d (γ B C₀ w X R C p : M.Domain) : Prop :=
  Rd_entry_d C₀ C p ∧ ∃ a V z t,
    Rr_layer_d I γ X R a z ∧ Rr_layer_d I B X R V t ∧ Rr_rank_d I X R a V ∧
    Rr_truth_d I X R (Formula.isLimitOrdinal .newest) (fun _ : Fin 1 => a) ∧
    Rd_entry_d w V R ∧ ∀ x y, Rd_entry_d x y t → Rd_entry_d x y p

theorem Tg_basis_d.anchor_l {γ B C₀ w X R C p : M.Domain}
    (h : Tg_basis_d I γ B C₀ w X R C p) : Tg_anchor_d I γ B X R p := by
  obtain ⟨_,a,V,z,t,height,layer,rank,_,_,fixed⟩ := h
  exact ⟨a,V,z,t,height,layer,rank,fixed⟩

variable (hZF : M.Models ZF)
local notation "J" => kp_pair_l (ZF.modelsKP hZF)

/-- 现有传递隶属初值直接产生原生基底；一般原模型随后使用同一关系证书。 -/
theorem Tg_basis_d.of_mem_l {γ B C₀ w c X R C p : M.Domain}
    (model : Smem_d J c X R) (trans : M.TransitiveSet X)
    (hγ : M.mem γ X) (hB : M.mem B X) (limit : M.IsLimitOrdinal γ) (rank : Vr_d X γ B)
    (omega : M.mem w B) (image : Rd_entry_d C₀ C p)
    (fixed : ∀ x, M.mem x B → Rd_entry_d x x p) : Tg_basis_d J γ B C₀ w X R C p := by
  obtain ⟨s,height,_⟩ := rr_layer_mem_l J hZF model trans hγ limit.1.transitive
  obtain ⟨t,layer,graph⟩ := rr_layer_mem_l J hZF model trans hB (rank.transitive_l trans hB)
  have truth : Rr_truth_d J X R (Formula.isLimitOrdinal .newest) (fun _ : Fin 1 => γ) := by
    let nx : Nonempty {x // M.mem x X} := ⟨⟨γ,hγ⟩⟩
    let ρ : Env (rt_model_l X nx) 1 := ⟨fun _ => ⟨γ,hγ⟩,fun _ => ⟨γ,hγ⟩⟩
    exact ⟨fun _ => hγ,(smem_formula_l J model nx _ ρ).mp
      ((Formula.satisfies_isLimitOrdinal_iff ..).mpr
        ((rt_limit_l trans nx (ZF.modelsKP hZF) ⟨γ,hγ⟩).mpr limit))⟩
  refine ⟨image,γ,B,s,t,height,layer,
    (rr_rank_mem_l J (ZF.modelsKP hZF) model trans hγ hB).mpr rank,truth,
    (model.2 w B).mpr ⟨trans B hB w omega,hB,omega⟩,?_⟩
  intro x y hxy
  obtain ⟨hx,rfl⟩ := (graph x y).mp hxy
  exact fixed x hx

end YesMetaZFC.SetTheory.LargeCardinal
