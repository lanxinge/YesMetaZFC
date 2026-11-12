import YesMetaZFC.SetTheory.LargeCardinal.Iteration.StepSyntax
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.Enumeration
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.BranchTail
import YesMetaZFC.SetTheory.Card.CountableUnion
import YesMetaZFC.SetTheory.LargeCardinal.Cardinals.ExternalBookkeeping
import YesMetaZFC.Model.SetTheory.Embedding.RankFixed

/-! # 原关系 ω 树的公共可数载体

实际收集所有模型的域并取并；每个域的可数性已由超幂和内部归纳证明。
对象选择只用于这一步可数并，之后的统一枚举仍用 ZF 的最小编号构造。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem it_countable_cover_l {ω c₀ T Q G E X₀ R₀ : M.Domain}
    (tree : It_tree_d hZF ω c₀ ω T Q G E) (mx : Smdl_d I c₀ X₀ R₀) (cx : M.CardinalLessOrEqual I X₀ ω) :
    ∃ Z ι, M.IsSetInjectionFromTo I ι Z ω ∧
      ∀ i c X R, Rd_entry_d i c Q → KPair_d M c X R → M.MemberSubset X Z := by
  have count := it_countable_l hZF tree mx cx
  obtain ⟨D, fq⟩ := tree.diagram.family_l hZF
  let φ : BinarySchema 1 := { body := .existsE (.existsE (.conj
    (rd_entry0_m (.bound 3) (.bound 1) (.bound 4)) (kpair_m (.bound 1) (.bound 2) .newest))) }
  let ρ : Env M 1 := ⟨fun _ => Q, fun _ => Q⟩
  have sat i X : φ.denote ρ i X ↔ ∃ c R, Rd_entry_d i c Q ∧ KPair_d M c X R := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      rd_entry0_sat_l hZF.1, kpair_sat_l M hZF.1]; rfl
  obtain ⟨U, us⟩ := ZF.exists_functionalImage hZF φ ρ ω (fun i hi => by
    obtain ⟨c, X, R, hc, mx⟩ := tree.diagram.model_l hZF hi
    exact ⟨X, (sat i X).mpr ⟨c, R, hc, mx.1⟩⟩) (fun i X Y hx hy => by
    obtain ⟨c, R, hc, mx⟩ := (sat i X).mp hx
    obtain ⟨d, S, hd, my⟩ := (sat i Y).mp hy
    exact (kpair_injective_l M mx ((tree.diagram.model_function.2 i d c hd hc) ▸ my)).1)
  obtain ⟨Z, hz⟩ := KP.exists_union (ZF.modelsKP hZF) U
  have sub i c X R (hc : Rd_entry_d i c Q) (hp : KPair_d M c X R) : M.MemberSubset X Z :=
    fun x hx => (hz x).mpr ⟨X, (us X).mpr ⟨i, (tree.diagram.model_domain i).mpr ⟨c, hc⟩, (sat i X).mpr ⟨c, R, hc, hp⟩⟩, hx⟩
  let ψ : BinarySchema 1 := { body := ep_at_m (.bound 2) (.bound 1) .newest }
  have psat i x : ψ.denote ρ i x ↔ Ep_at_d Q i x := ep_at_sat_l hZF.1 ..
  obtain ⟨id, hid⟩ := ZF.exists_identityBijection hZF I ω
  obtain ⟨ι, hι⟩ := ZFC.countable_cover_l I hZFC tree.omega ψ ρ ⟨id, hid.1⟩ (X := Z) (by
    intro i hi B bs
    obtain ⟨c, X, R, hc, mx⟩ := tree.diagram.model_l hZF hi
    have eq : B = X := hZF.1.eq_of_same_members B X (fun x => (bs x).trans
      ⟨fun h => (ep_at_read_l fq hc mx.1).mp ((psat i x).mp h.2),
        fun hx => ⟨sub i c X R hc mx.1 x hx, (psat i x).mpr ((ep_at_read_l fq hc mx.1).mpr hx)⟩⟩)
    exact eq.symm ▸ count i c X R hc mx.1) (by
    intro x hx
    obtain ⟨X, hX, hxX⟩ := (hz x).mp hx
    obtain ⟨i, hi, hs⟩ := (us X).mp hX
    obtain ⟨c, R, hc, hp⟩ := (sat i X).mp hs
    exact ⟨i, hi, (psat i x).mpr ⟨c, X, R, hc, hp, hxX⟩⟩)
  exact ⟨Z, ι, hι, sub⟩

/-! 可数根到整条尝试枚举的闭合入口。

`it_countable_cover_l` 只给出所有阶段模型的公共载体；`ja_enum_l` 再把该载体
转成每一行的实际有限序列编号。这个接口把两步合并，后续复制与 branch
bookkeeping 只需消费一个 `Ja_enum_d`，不会重新引入额外的外部可数性假设。
-/
theorem It_tree_d.ja_enum_l {ω c₀ T Q G E X₀ R₀ : M.Domain}
    (hZFC : M.Models ZFC) (tree : It_tree_d (ZFC.models_zf_l hZFC) ω c₀ ω T Q G E)
    (mx : Smdl_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) c₀ X₀ R₀)
    (cx : M.CardinalLessOrEqual (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) X₀ ω) :
    ∃ E', Ja_enum_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω ω Q E' := by
  obtain ⟨Z, ι, count, cover⟩ := it_countable_cover_l hZFC tree mx cx
  exact YesMetaZFC.SetTheory.LargeCardinal.ja_enum_l
    (ZFC.models_zf_l hZFC) tree.omega tree.diagram count cover

/-! owner 与逐行枚举的第一次真正接合。

极限模型中的任意成员先由锥的 `owner_mem_l` 拉回某个阶段；阶段属于原
diagram 后，`Ja_enum_d` 给出该阶段模型的 ω 行及其逐点覆盖。这里保留
owner 图和源行，不把它误写成目标集合本身已有枚举。 -/
theorem It_cone_d.owner_row_countable_l
    (hZF0 : M.Models ZF) {ω α T Q G B d N W P A Ec : M.Domain}
    (diagram : It_diagram_d (kp_pair_l (ZF.modelsKP hZF0)) ω α T Q G)
    (inside : M.MemberSubset B α)
    (en : Ja_enum_d (kp_pair_l (ZF.modelsKP hZF0)) ω α Q Ec)
    (cone : It_cone_d (kp_pair_l (ZF.modelsKP hZF0)) ω B Q G d N W P)
    (transitive : M.TransitiveSet N) (hA : M.mem A N) :
    ∀ y, M.mem y A → ∃ i f x e c X R,
      Rd_entry_d i f P ∧ Rd_entry_d x y f ∧ Rd_entry_d i e Ec ∧
      Rd_entry_d i c Q ∧ Smdl_d (kp_pair_l (ZF.modelsKP hZF0)) c X R ∧
      Fn0_d ω X e ∧ ∀ z, M.mem z X → ∃ n, M.mem n ω ∧ Rd_entry_d n z e := by
  intro y hy
  obtain ⟨i, f, x, hf, hxy⟩ := cone.owner_mem_l transitive hA y hy
  have hiB : M.mem i B := (cone.domain i).mpr ⟨f, hf⟩
  have hiα : M.mem i α := inside i hiB
  obtain ⟨e, he⟩ := (en.domain i).mp hiα
  obtain ⟨c, X, R, hc, mx⟩ := diagram.model_l hZF0 hiα
  obtain ⟨fe, row⟩ := en.row_countable_l (kp_pair_l (ZF.modelsKP hZF0)) he hc mx.1
  exact ⟨i, f, x, e, c, X, R, hf, hxy, he, hc, mx, fe, row⟩

/-! owner 代表的三坐标关系：阶段码、阶段行码和行内 ω 坐标。
它把阶段行的覆盖见证压缩成正好可由 `Bk_owner_code` 枚举的外部代码。 -/
def It_owner_code_d {M : Structure} (P Ec Q y i e n : M.Domain) : Prop :=
  ∃ f x c X R, Rd_entry_d i f P ∧ Rd_entry_d x y f ∧ Rd_entry_d i e Ec ∧
    Rd_entry_d i c Q ∧ KPair_d M c X R ∧ Rd_entry_d n x e

theorem It_cone_d.owner_code_l
    (hZF0 : M.Models ZF) {ω α T Q G B d N W P A Ec : M.Domain}
    (diagram : It_diagram_d (kp_pair_l (ZF.modelsKP hZF0)) ω α T Q G)
    (inside : M.MemberSubset B α)
    (en : Ja_enum_d (kp_pair_l (ZF.modelsKP hZF0)) ω α Q Ec)
    (cone : It_cone_d (kp_pair_l (ZF.modelsKP hZF0)) ω B Q G d N W P)
    (transitive : M.TransitiveSet N) (hA : M.mem A N) :
    ∀ y, M.mem y A → ∃ i e n, M.mem i α ∧ M.mem n ω ∧ It_owner_code_d P Ec Q y i e n := by
  intro y hy
  obtain ⟨i, f, x, e, c, X, R, hf, hxy, he, hc, mx, fe, row⟩ :=
    cone.owner_row_countable_l hZF0 diagram inside en transitive hA y hy
  have hiα : M.mem i α := inside i ((cone.domain i).mpr ⟨f, hf⟩)
  have stage := cone.elementary i f c X R hf hc mx
  have hxX := stage.1.1.input_mem_of_pairMember hxy
  obtain ⟨n, hn, hnx⟩ := row x hxX
  exact ⟨i, e, n, hiα, hn, f, x, c, X, R, hf, hxy, he, hc, mx.1, hnx⟩

theorem It_cone_d.owner_code_cover_l
    (hZF0 : M.Models ZF) {ω α T Q G B d N W P A Ec : M.Domain}
    (diagram : It_diagram_d (kp_pair_l (ZF.modelsKP hZF0)) ω α T Q G)
    (inside : M.MemberSubset B α)
    (en : Ja_enum_d (kp_pair_l (ZF.modelsKP hZF0)) ω α Q Ec)
    (cone : It_cone_d (kp_pair_l (ZF.modelsKP hZF0)) ω B Q G d N W P)
    (transitive : M.TransitiveSet N) (hA : M.mem A N) :
    ∀ y, M.mem y A → ∃ c : Bk_owner_code M.Domain,
      It_owner_code_d P Ec Q y c.1.1 c.1.2 c.2 := by
  intro y hy
  obtain ⟨i, e, n, _, _, code⟩ := cone.owner_code_l hZF0 diagram inside en transitive hA y hy
  exact ⟨((i, e), n), code⟩

/-! 若所选嵌入的源端已经给出一个可数的传递对象，则其像对象的代表图
可以直接读回目标载体。`Smap_d.countable_fixed_l` 同时构造逐点固定图和
目标端的 ω 单射；这里抽取的 `A ↦ A` 图正是后续 `j(U₁) ∈ N` bookkeeping
所需的代表字段。 -/
theorem Smap_d.countable_fixed_mem_l
    (hZF0 : M.Models ZF)
    {ω c d X R Y S j A ι : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d (kp_pair_l (ZF.modelsKP hZF0)) c X R)
    (hn : Smem_d (kp_pair_l (ZF.modelsKP hZF0)) d Y S)
    (map : Smap_d (kp_pair_l (ZF.modelsKP hZF0)) ω c d X Y j)
    (hωX : M.mem ω X) (hA : M.mem A X) (hAt : M.TransitiveSet A)
    (hι : M.mem ι X)
    (inj : M.IsSetInjectionFromTo (kp_pair_l (ZF.modelsKP hZF0)) ι A ω) :
    M.mem A Y := by
  obtain ⟨hAA, _, _⟩ := map.countable_fixed_l hZF0 hω hX hY hm hn hωX hA hAt hι inj
  exact map.1.1.output_mem_of_pairMember hAA

/-! 把 owner 沿分支前端实际运输到更高节点。

这里使用 `It_branch_d.forward_l` 而不是把序数成员关系直接当成树边。
前端的低节点本身来自锥的 `P` 域，故属于分支；分支的链性再给出真正的
`T` 关系。组合图把原 owner 的值改写成高节点 owner，最后重新读取高节点行
的外部 ω 坐标。 -/
theorem It_cone_d.owner_code_front_l
    (hZF0 : M.Models ZF) {ω α T Q G B d N W P A Ec : M.Domain}
    (diagram : It_diagram_d (kp_pair_l (ZF.modelsKP hZF0)) ω α T Q G)
    (inside : M.MemberSubset B α)
    (en : Ja_enum_d (kp_pair_l (ZF.modelsKP hZF0)) ω α Q Ec)
    (cone : It_cone_d (kp_pair_l (ZF.modelsKP hZF0)) ω B Q G d N W P)
    (transitive : M.TransitiveSet N) (hA : M.mem A N)
    (branch : It_branch_d α T B)
    (enum : Nat → M.Domain) (enum_sub : ∀ n, M.mem (enum n) α)
    (slot : ∀ j, M.mem j B → Nat → Nat)
    (replete : ∀ j hj k, k < slot j hj k ∧ enum (slot j hj k) = j) :
    ∀ y, M.mem y A → ∀ k, ∃ m i e n,
      k < m ∧ It_front_d α B i (enum m) ∧ M.mem i B ∧ M.mem n ω ∧
        It_owner_code_d P Ec Q y (enum m) e n := by
  intro y hy k
  obtain ⟨i, f, x, e, c, X, R, hf, hxy, he, hc, mx, fe, row⟩ :=
    cone.owner_row_countable_l hZF0 diagram inside en transitive hA y hy
  have hiB : M.mem i B := (cone.domain i).mpr ⟨f, hf⟩
  have hiα : M.mem i α := inside i hiB
  obtain ⟨m, hm, hfront⟩ :=
    branch.external_front_code_l enum slot replete i hiα k
  have hjB : M.mem (enum m) B := hfront.2.1
  have hij : Rd_entry_d i (enum m) T :=
    branch.forward_l diagram.order hiB hjB hfront.2.2
  obtain ⟨g, hmap⟩ := diagram.map_l hZF0 hij
  obtain ⟨v, hv⟩ := (cone.domain (enum m)).mp hjB
  have comp := It_embedding_d.comp_l hZF0 diagram branch.subset
    cone.toIt_embedding_d hmap hf hv
  obtain ⟨z, hxz, hzy⟩ := (comp.2 x y).mp hxy
  have hjα : M.mem (enum m) α := enum_sub m
  obtain ⟨c', X', R', hc', mx'⟩ := diagram.model_l hZF0 hjα
  obtain ⟨e', he'⟩ := (en.domain (enum m)).mp hjα
  obtain ⟨_, row'⟩ := en.row_countable_l
    (kp_pair_l (ZF.modelsKP hZF0)) he' hc' mx'.1
  have stage' := cone.elementary (enum m) v c' X' R' hv hc' mx'
  have hzX : M.mem z X' := stage'.1.1.input_mem_of_pairMember hzy
  obtain ⟨n, hn, hzn⟩ := row' z hzX
  refine ⟨m, i, e', n, hm, hfront, hiB, hn, ?_⟩
  exact ⟨v, z, c', X', R', hv, hzy, he', hc', mx'.1, hzn⟩

/-! 固定一个 branch front 后的 owner transport 核心。

该接口不负责选择 front，只消费已有 owner 图和 `It_front_d`，因此可以和
`IterationBranchSchedule.chain_l` 组合，构造 eventual `decode/extend`。 -/
theorem It_cone_d.owner_code_transport_l
    (hZF0 : M.Models ZF) {ω α T Q G B d N W P Ec i j f x y : M.Domain}
    (diagram : It_diagram_d (kp_pair_l (ZF.modelsKP hZF0)) ω α T Q G)
    (en : Ja_enum_d (kp_pair_l (ZF.modelsKP hZF0)) ω α Q Ec)
    (cone : It_cone_d (kp_pair_l (ZF.modelsKP hZF0)) ω B Q G d N W P)
    (branch : It_branch_d α T B)
    (hf : Rd_entry_d i f P) (hxy : Rd_entry_d x y f)
    (hfront : It_front_d α B i j) :
    ∃ e n, M.mem n ω ∧ It_owner_code_d P Ec Q y j e n := by
  have hiB : M.mem i B := (cone.domain i).mpr ⟨f, hf⟩
  have hij : Rd_entry_d i j T :=
    branch.forward_l diagram.order hiB hfront.2.1 hfront.2.2
  obtain ⟨g, hmap⟩ := diagram.map_l hZF0 hij
  obtain ⟨v, hv⟩ := (cone.domain j).mp hfront.2.1
  have comp := It_embedding_d.comp_l hZF0 diagram branch.subset
    cone.toIt_embedding_d hmap hf hv
  obtain ⟨z, hxz, hzy⟩ := (comp.2 x y).mp hxy
  have hjα : M.mem j α := branch.subset j hfront.2.1
  obtain ⟨c, X, R, hc, mx⟩ := diagram.model_l hZF0 hjα
  obtain ⟨e, he⟩ := (en.domain j).mp hjα
  obtain ⟨_, row⟩ := en.row_countable_l
    (kp_pair_l (ZF.modelsKP hZF0)) he hc mx.1
  have stage := cone.elementary j v c X R hv hc mx
  have hzX : M.mem z X := stage.1.1.input_mem_of_pairMember hzy
  obtain ⟨n, hn, hzn⟩ := row z hzX
  exact ⟨e, n, hn, ⟨v, z, c, X, R, hv, hzy, he, hc, mx.1, hzn⟩⟩

/-! 将上一接口专门化到显式可数的阶段枚举。 -/
theorem It_cone_d.owner_code_front_countable_l
    (hZF0 : M.Models ZF) {ω α T Q G B d N W P A Ec : M.Domain}
    (diagram : It_diagram_d (kp_pair_l (ZF.modelsKP hZF0)) ω α T Q G)
    (inside : M.MemberSubset B α)
    (en : Ja_enum_d (kp_pair_l (ZF.modelsKP hZF0)) ω α Q Ec)
    (cone : It_cone_d (kp_pair_l (ZF.modelsKP hZF0)) ω B Q G d N W P)
    (transitive : M.TransitiveSet N) (hA : M.mem A N)
    (branch : It_branch_d α T B)
    (count : Bk_countable {c : M.Domain // M.mem c α})
    (slot : ∀ j, M.mem j B → Nat → Nat)
    (replete : ∀ j hj k, k < slot j hj k ∧
      count.enum (YesMetaZFC.Logic.Arithmetic.NatPairing.unpair_l
        (slot j hj k)).1 = ⟨j, branch.subset j hj⟩) :
    ∀ y, M.mem y A → ∀ k, ∃ m i e n,
      k < m ∧ It_front_d α B i
        ((count.enum (YesMetaZFC.Logic.Arithmetic.NatPairing.unpair_l m).1).1) ∧
      M.mem i B ∧ M.mem n ω ∧
        It_owner_code_d P Ec Q y
          (count.enum (YesMetaZFC.Logic.Arithmetic.NatPairing.unpair_l m).1).1 e n := by
  let enum : Nat → M.Domain := fun n =>
    (count.enum (YesMetaZFC.Logic.Arithmetic.NatPairing.unpair_l n).1).1
  have enum_sub : ∀ n, M.mem (enum n) α := by
    intro n
    exact (count.enum (YesMetaZFC.Logic.Arithmetic.NatPairing.unpair_l n).1).2
  have replete' : ∀ (j : M.Domain) (hj : M.mem j B) (k : Nat),
      k < slot j hj k ∧ enum (slot j hj k) = j := by
    intro j hj k
    have h := replete j hj k
    exact ⟨h.1, congrArg Subtype.val h.2⟩
  simpa only [enum] using
    (cone.owner_code_front_l hZF0 diagram inside en transitive hA branch
      enum enum_sub slot replete')

/-! 阶段枚举已给定时，自动生成分支 slot 的 owner 前端出口。 -/
theorem It_cone_d.owner_code_front_auto_l
    (hZF0 : M.Models ZF) {ω α T Q G B d N W P A Ec : M.Domain}
    (diagram : It_diagram_d (kp_pair_l (ZF.modelsKP hZF0)) ω α T Q G)
    (inside : M.MemberSubset B α)
    (en : Ja_enum_d (kp_pair_l (ZF.modelsKP hZF0)) ω α Q Ec)
    (cone : It_cone_d (kp_pair_l (ZF.modelsKP hZF0)) ω B Q G d N W P)
    (transitive : M.TransitiveSet N) (hA : M.mem A N)
    (branch : It_branch_d α T B)
    (count : Bk_countable {c : M.Domain // M.mem c α}) :
    ∀ y, M.mem y A → ∀ k, ∃ m i e n,
      k < m ∧ It_front_d α B i
        ((count.enum (YesMetaZFC.Logic.Arithmetic.NatPairing.unpair_l m).1).1) ∧
      M.mem i B ∧ M.mem n ω ∧
        It_owner_code_d P Ec Q y
          (count.enum (YesMetaZFC.Logic.Arithmetic.NatPairing.unpair_l m).1).1 e n := by
  let slot : ∀ j, M.mem j B → Nat → Nat := fun j hj k =>
    YesMetaZFC.Logic.Arithmetic.NatPairing.pair_l
      (count.pick ⟨j, branch.subset j hj⟩) (k + 1)
  have replete : ∀ j hj k, k < slot j hj k ∧
      count.enum (YesMetaZFC.Logic.Arithmetic.NatPairing.unpair_l
        (slot j hj k)).1 = ⟨j, branch.subset j hj⟩ := by
    intro j hj k
    simpa only [slot] using
      (count.replete_l (c := ⟨j, branch.subset j hj⟩) k)
  exact It_cone_d.owner_code_front_countable_l hZF0 diagram inside en cone
    transitive hA branch count slot replete

/-! 三段运输的相容性。`direct` 是树上两步 map 的复合图，左右两段由
同一个 cone 的 owner embedding 产生；`It_comp_d.assoc_l` 因而给出直接 map
到末端 owner 的 transport coherence。 -/
theorem It_cone_d.owner_transport_assoc_l
    (hZF0 : M.Models ZF) {ω α T Q G B d N W P i j k f g h u v w : M.Domain}
    (diagram : It_diagram_d (kp_pair_l (ZF.modelsKP hZF0)) ω α T Q G)
    (inside : M.MemberSubset B α)
    (cone : It_cone_d (kp_pair_l (ZF.modelsKP hZF0)) ω B Q G d N W P)
    (direct : It_comp_d f g h)
    (hf : It_map_d G i j f) (hg : It_map_d G j k g)
    (hu : Rd_entry_d i u P) (hv : Rd_entry_d j v P) (hw : Rd_entry_d k w P) :
    It_comp_d h w u := by
  have left := It_embedding_d.comp_l hZF0 diagram inside cone.toIt_embedding_d hf hu hv
  have middle := It_embedding_d.comp_l hZF0 diagram inside cone.toIt_embedding_d hg hv hw
  exact It_comp_d.assoc_l direct middle left

/-! 允许在外部使用显式选择时，从内部 `Smap_d` 图读取 host 值。
`value_l` 保留图成员性和目标成员性，后续 Bk system 可直接消费这个 section。 -/
noncomputable def Smap_d.value_l
    {M : Structure} {𝒞 : OrderedPairConvention} {ι : 𝒞.Interpretation M}
    {ω c d X Y j x : M.Domain}
    (h : Smap_d ι ω c d X Y j) (hx : M.mem x X) : M.Domain :=
  Classical.choose (h.1.1.2.2 x hx)

theorem Smap_d.value_mem_l
    {M : Structure} {𝒞 : OrderedPairConvention} {ι : 𝒞.Interpretation M}
    {ω c d X Y j x : M.Domain}
    (h : Smap_d ι ω c d X Y j) (hx : M.mem x X) :
    M.mem (Smap_d.value_l h hx) Y :=
  (Classical.choose_spec (h.1.1.2.2 x hx)).1

theorem Smap_d.value_graph_l
    {M : Structure} {𝒞 : OrderedPairConvention} {ι : 𝒞.Interpretation M}
    {ω c d X Y j x : M.Domain}
    (h : Smap_d ι ω c d X Y j) (hx : M.mem x X) :
    M.PairMember ι x (Smap_d.value_l h hx) j :=
  (Classical.choose_spec (h.1.1.2.2 x hx)).2

/-! 行代码沿一个阶段函数运输到目标集合时的可数覆盖。

这里把“目标正好是该阶段像”作为显式满射条件；在此条件下，函数图复合
给出目标的真实 ω 行，并保留复合图方程，供后续 branch coherence 直接读取。
-/
theorem Ja_enum_d.row_transport_l
    {ω e X f A : M.Domain}
    (hZF0 : M.Models ZF) (row : Fn0_d ω X e)
    (row_cover : ∀ x, M.mem x X → ∃ n, M.mem n ω ∧ Rd_entry_d n x e)
    (map : M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hZF0)) f X A)
    (onto : M.IsSetSurjectiveOnto (kp_pair_l (ZF.modelsKP hZF0)) f X A) :
    ∃ g, Fn0_d ω A g ∧
      (∀ n y, Rd_entry_d n y g ↔ M.mem n ω ∧
        ∃ x, Rd_entry_d n x e ∧ Rd_entry_d x y f) ∧
      ∀ y, M.mem y A → ∃ n, M.mem n ω ∧ Rd_entry_d n y g := by
  obtain ⟨g, hg, graph⟩ := ZF.exists_compositionFunction hZF0
    (kp_pair_l (ZF.modelsKP hZF0)) (fn0_function_l (ZF.modelsKP hZF0) row) map
  have fn : Fn0_d ω A g := fn0_of_function_l (ZF.modelsKP hZF0) hg
  have cover : ∀ y, M.mem y A → ∃ n, M.mem n ω ∧ Rd_entry_d n y g := by
    intro y hy
    obtain ⟨x, hx, hxy⟩ := onto y hy
    obtain ⟨n, hn, hnx⟩ := row_cover x hx
    exact ⟨n, hn, (graph n y).mpr ⟨hn, x, hnx, hxy⟩⟩
  exact ⟨g, fn, graph, cover⟩

end YesMetaZFC.SetTheory.LargeCardinal
