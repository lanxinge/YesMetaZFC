import YesMetaZFC.Model.Arithmetic.PrimitiveRecursive.NatPairing

/-! # 外部代码的相容 bookkeeping

本层只处理调度本身。`decode` 负责把一个外部代码解释成每个阶段的对象，
`transport` 负责阶段间搬运；代码解释的相容性与无限重复枚举共同产生
eventual coverage。目标代码空间、代表压缩和 owner 证明仍由上游定理提供。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal

universe u v w q

structure Bk_system (C : Type u) (S : Nat → Type v) where
  decode : ∀ n, C → S n
  transport : ∀ {m n}, m ≤ n → S m → S n
  coherent : ∀ {m n} (h : m ≤ n) (c : C),
    transport h (decode m c) = decode n c

/-! 一个 `Bk_countable` 同时保存枚举和其显式 section。这样从外部可数性到
无限重复枚举的转换是可计算的，不使用 `Classical.choose`。 -/
structure Bk_countable (C : Type u) where
  enum : Nat → C
  pick : C → Nat
  pick_spec : ∀ c, enum (pick c) = c

/-! ZFC 下可由满射选择 section。此构造明确标记为 noncomputable，供外部
可数模型接入，不再把 section 当成可计算数据伪造。 -/
noncomputable def Bk_countable.of_surjective {C : Type u}
    (enum : Nat → C) (surjective : Function.Surjective enum) : Bk_countable C where
  enum := enum
  pick c := Classical.choose (surjective c)
  pick_spec c := Classical.choose_spec (surjective c)

/-! 可数空间的任意非空子类型仍有显式枚举。落在子类型外的编号统一回退到
一个固定成员，原枚举的 section 保证每个子类型成员仍在其原编号处出现。 -/
noncomputable def Bk_countable.subtype {D : Type u} (count : Bk_countable D)
    (P : D → Prop) (nonempty : ∃ d, P d) : Bk_countable {d : D // P d} := by
  classical
  let d₀ : D := Classical.choose nonempty
  let hd₀ : P d₀ := Classical.choose_spec nonempty
  let e : Nat → {d : D // P d} := fun n =>
    if hn : P (count.enum n) then ⟨count.enum n, hn⟩ else ⟨d₀, hd₀⟩
  refine { enum := e, pick := fun c => count.pick c.1, pick_spec := ?_ }
  intro c
  dsimp [e]
  have hc : count.enum (count.pick c.1) = c.1 := count.pick_spec c.1
  rw [hc]
  simp only [dif_pos c.2]

/-! 显式可数空间对有限乘积封闭；代码元组因此不需要额外的外部选择。 -/
def Bk_countable.prod {A : Type u} {B : Type v}
    (left : Bk_countable A) (right : Bk_countable B) : Bk_countable (A × B) where
  enum n := (left.enum
      (YesMetaZFC.Logic.Arithmetic.NatPairing.unpair_l n).1,
    right.enum (YesMetaZFC.Logic.Arithmetic.NatPairing.unpair_l n).2)
  pick p := YesMetaZFC.Logic.Arithmetic.NatPairing.pair_l
    (left.pick p.1) (right.pick p.2)
  pick_spec p := by
    simp only [YesMetaZFC.Model.Arithmetic.PrimitiveRecursive.unpair_pair_l,
      left.pick_spec, right.pick_spec]

def Bk_countable.nat : Bk_countable Nat where
  enum n := n
  pick n := n
  pick_spec _ := rfl

/-! owner 代码的标准形状：阶段码、阶段行码和模型内部自然数坐标。 -/
abbrev Bk_owner_code (D : Type u) := (D × D) × D

def Bk_countable.owner_code_l {D : Type u} (count : Bk_countable D) :
    Bk_countable (Bk_owner_code D) :=
  Bk_countable.prod (Bk_countable.prod count count) count

/-! `Bk_cover` 把 bookkeeping 与实际目标的凝聚图分开。`owner` 只要求目标值
先在某一阶段代码中出现；`embed_coherent` 再把阶段间运输识别成同一目标值。
-/
structure Bk_cover (C : Type u) (S : Nat → Type v) (Y : Type w) where
  system : Bk_system C S
  embed : ∀ n, S n → Y
  embed_coherent : ∀ {m n} (h : m ≤ n) (c : C),
    embed n (system.transport h (system.decode m c)) = embed m (system.decode m c)
  owner : ∀ y : Y, ∃ m c, embed m (system.decode m c) = y

/-- `slot` 给出每个代码的无限次未来出现；这是调度所需的最弱重复枚举接口。 -/
def Bk_replete (enum : Nat → C) (slot : C → Nat → Nat) : Prop :=
  ∀ c k, k < slot c k ∧ enum (slot c k) = c

theorem Bk_countable.replete_l {C : Type u} (count : Bk_countable C) :
    Bk_replete (fun n => count.enum
      (YesMetaZFC.Logic.Arithmetic.NatPairing.unpair_l n).1)
      (fun c k => YesMetaZFC.Logic.Arithmetic.NatPairing.pair_l (count.pick c) (k + 1)) := by
  intro c k
  by_cases h : count.pick c < k + 1
  · change k < YesMetaZFC.Logic.Arithmetic.NatPairing.pair_l (count.pick c) (k + 1) ∧
      count.enum (YesMetaZFC.Logic.Arithmetic.NatPairing.unpair_l
        (YesMetaZFC.Logic.Arithmetic.NatPairing.pair_l (count.pick c) (k + 1))).1 = c
    have h₁ : k < k + 1 := Nat.lt_succ_self k
    have h₂ : k + 1 ≤ (k + 1) * (k + 1) :=
      Nat.le_mul_of_pos_right (k + 1) (Nat.zero_lt_succ k)
    constructor
    · dsimp [YesMetaZFC.Logic.Arithmetic.NatPairing.pair_l]
      rw [if_pos h]
      omega
    · simp only [YesMetaZFC.Model.Arithmetic.PrimitiveRecursive.unpair_pair_l,
        count.pick_spec]

  · change k < YesMetaZFC.Logic.Arithmetic.NatPairing.pair_l (count.pick c) (k + 1) ∧
      count.enum (YesMetaZFC.Logic.Arithmetic.NatPairing.unpair_l
        (YesMetaZFC.Logic.Arithmetic.NatPairing.pair_l (count.pick c) (k + 1))).1 = c
    have h₁ : k < k + 1 := Nat.lt_succ_self k
    have hn : k + 1 ≤ count.pick c := by omega
    have h₂ : count.pick c ≤ count.pick c * count.pick c + count.pick c + (k + 1) := by
      exact Nat.le_trans (Nat.le_add_left (count.pick c) (count.pick c * count.pick c))
        (Nat.le_add_right (count.pick c * count.pick c + count.pick c) (k + 1))
    constructor
    · dsimp [YesMetaZFC.Logic.Arithmetic.NatPairing.pair_l]
      rw [if_neg h]
      exact Nat.lt_of_lt_of_le h₁ (Nat.le_trans hn h₂)
    · simp only [YesMetaZFC.Model.Arithmetic.PrimitiveRecursive.unpair_pair_l,
        count.pick_spec]

/-! 带 owner stage 下界的重复枚举。 -/
def Bk_countable.tail_slot {C : Type u} (count : Bk_countable C)
    (stage : C → Nat) (c : C) (k : Nat) : Nat :=
  YesMetaZFC.Logic.Arithmetic.NatPairing.pair_l (count.pick c)
    (max k (stage c) + 1)

theorem Bk_countable.tail_replete_l {C : Type u} (count : Bk_countable C)
    (stage : C → Nat) :
    ∀ c k, k < count.tail_slot stage c k ∧ stage c ≤ count.tail_slot stage c k ∧
      count.enum (YesMetaZFC.Logic.Arithmetic.NatPairing.unpair_l
        (count.tail_slot stage c k)).1 = c := by
  intro c k
  let q := max k (stage c)
  have h := count.replete_l c q
  have hq : q < YesMetaZFC.Logic.Arithmetic.NatPairing.pair_l
      (count.pick c) (q + 1) := h.1
  have hkq : k ≤ q := Nat.le_max_left _ _
  have hsq : stage c ≤ q := Nat.le_max_right _ _
  refine ⟨Nat.lt_of_le_of_lt hkq ?_, Nat.le_trans hsq ?_, ?_⟩
  · simpa only [Bk_countable.tail_slot, q] using hq
  · simpa only [Bk_countable.tail_slot, q] using (Nat.le_of_lt hq)
  · simpa only [Bk_countable.tail_slot, q] using h.2
/-- 无限重复枚举首先必须是满射；因此外部代码空间的可数性不是调度层可省略的条件。 -/
theorem Bk_replete.surjective {C : Type u} {enum : Nat → C} {slot : C → Nat → Nat}
    (h : Bk_replete enum slot) : Function.Surjective enum := by
  intro c
  exact ⟨slot c 0, (h c 0).2⟩

/-- 相容代码在所有阶段的解释可由一条实际序列逐项覆盖。 -/
theorem Bk_system.schedule_l {C : Type u} {S : Nat → Type v}
    (sys : Bk_system C S) (enum : Nat → C) (slot : C → Nat → Nat)
    (replete : Bk_replete enum slot) :
    ∃ z : ∀ n, S n, ∀ m c, ∃ n, ∃ h : m < n,
      z n = sys.transport (Nat.le_of_lt h) (sys.decode m c) := by
  refine ⟨fun n => sys.decode n (enum n), ?_⟩
  intro m c
  let n := slot c (m + 1)
  have hn : m + 1 < n := (replete c (m + 1)).1
  have hmn : m < n := Nat.lt_trans (Nat.lt_succ_self m) hn
  have hcode : enum n = c := (replete c (m + 1)).2
  refine ⟨n, hmn, ?_⟩
  have hcoh := sys.coherent (Nat.le_of_lt hmn) c
  calc
    (fun n => sys.decode n (enum n)) n = sys.decode n (enum n) := rfl
    _ = sys.decode n c := by rw [hcode]
    _ = sys.transport (Nat.le_of_lt hmn) (sys.decode m c) := hcoh.symm

/-! 把显式可数代码空间直接送入调度器。 -/
theorem Bk_system.schedule_countable_l {C : Type u} {S : Nat → Type v}
    (sys : Bk_system C S) (count : Bk_countable C) :
    ∃ z : ∀ n, S n, ∀ m c, ∃ n, ∃ h : m < n,
      z n = sys.transport (Nat.le_of_lt h) (sys.decode m c) := by
  exact sys.schedule_l
    (fun n => count.enum
      (YesMetaZFC.Logic.Arithmetic.NatPairing.unpair_l n).1)
    (fun c k => YesMetaZFC.Logic.Arithmetic.NatPairing.pair_l (count.pick c) (k + 1))
    count.replete_l

/-! 带分支命中前端的调度。

`front` 只描述树的结构：每个代码在每条分支上都有任意晚的命中点；
它不包含目标值或 eventual coverage。调度序列仍由同一个全局 `enum` 产生，
因此 coherence 才能把命中点的值识别为祖先阶段的运输像。 -/
theorem Bk_system.branch_schedule_l
    {C : Type u} {S : Nat → Type v} {B : Type q}
    (sys : Bk_system C S) (enum : Nat → C) (front : C → Nat → Nat)
    (replete : ∀ c k, k < front c k ∧ enum (front c k) = c)
    (branch : B → Nat → Prop)
    (hit : ∀ b m c, ∃ k, m < front c k ∧ branch b (front c k)) :
    ∃ z : ∀ n, S n, ∀ b m c, ∃ n, branch b n ∧ ∃ h : m < n,
      z n = sys.transport (Nat.le_of_lt h) (sys.decode m c) := by
  refine ⟨fun n => sys.decode n (enum n), ?_⟩
  intro b m c
  obtain ⟨k, hmk, hbranch⟩ := hit b m c
  let n := front c k
  have hcode : enum n = c := (replete c k).2
  have hcoh := sys.coherent (Nat.le_of_lt hmk) c
  refine ⟨n, hbranch, hmk, ?_⟩
  calc
    (fun n => sys.decode n (enum n)) n = sys.decode n (enum n) := rfl
    _ = sys.decode n c := by rw [hcode]
    _ = sys.transport (Nat.le_of_lt hmk) (sys.decode m c) := hcoh.symm

theorem Bk_system.branch_schedule_countable_l
    {C : Type u} {S : Nat → Type v} {B : Type q}
    (sys : Bk_system C S) (count : Bk_countable C) (front : C → Nat → Nat)
    (replete : ∀ c k, k < front c k ∧
      (fun n => count.enum
        (YesMetaZFC.Logic.Arithmetic.NatPairing.unpair_l n).1) (front c k) = c)
    (branch : B → Nat → Prop)
    (hit : ∀ b m c, ∃ k, m < front c k ∧ branch b (front c k)) :
    ∃ z : ∀ n, S n, ∀ b m c, ∃ n, branch b n ∧ ∃ h : m < n,
      z n = sys.transport (Nat.le_of_lt h) (sys.decode m c) := by
  exact sys.branch_schedule_l
    (fun n => count.enum
      (YesMetaZFC.Logic.Arithmetic.NatPairing.unpair_l n).1)
    front replete branch hit

/-! 强覆盖—凝聚的组合定理。

它只把四个可审计接口接在一起：代码的阶段相容性、每个目标值的 owner、
代码的无限重复出现，以及每条分支对每个 owner 的任意晚 front 命中。结论
给出一条统一阶段序列，并把每个 owner 运输到分支命中点；没有把目标覆盖
或运输一致性隐藏在结论中。 -/
theorem Bk_cover.condensation_l
    {C : Type u} {S : Nat → Type v} {Y : Type w} {B : Type q}
    (cover : Bk_cover C S Y) (enum : Nat → C) (front : C → Nat → Nat)
    (replete : ∀ c k, k < front c k ∧ enum (front c k) = c)
    (branch : B → Nat → Prop)
    (hit : ∀ b m c, ∃ k, m < front c k ∧ branch b (front c k)) :
    ∃ z : ∀ n, S n, ∀ b y, ∃ n, branch b n ∧
      ∃ m c, cover.embed m (cover.system.decode m c) = y ∧
        cover.embed n (z n) = y := by
  obtain ⟨z, hz⟩ := Bk_system.branch_schedule_l cover.system enum front replete branch hit
  refine ⟨z, ?_⟩
  intro b y
  obtain ⟨m, c, howner⟩ := cover.owner y
  obtain ⟨n, hbranch, hmn, htransport⟩ := hz b m c
  refine ⟨n, hbranch, m, c, howner, ?_⟩
  rw [htransport]
  exact (cover.embed_coherent (Nat.le_of_lt hmn) c).trans howner

theorem Bk_cover.condensation_countable_l
    {C : Type u} {S : Nat → Type v} {Y : Type w} {B : Type q}
    (cover : Bk_cover C S Y) (count : Bk_countable C) (front : C → Nat → Nat)
    (replete : ∀ c k, k < front c k ∧
      (fun n => count.enum
        (YesMetaZFC.Logic.Arithmetic.NatPairing.unpair_l n).1) (front c k) = c)
    (branch : B → Nat → Prop)
    (hit : ∀ b m c, ∃ k, m < front c k ∧ branch b (front c k)) :
    ∃ z : ∀ n, S n, ∀ b y, ∃ n, branch b n ∧
      ∃ m c, cover.embed m (cover.system.decode m c) = y ∧
        cover.embed n (z n) = y := by
  exact cover.condensation_l
    (fun n => count.enum
      (YesMetaZFC.Logic.Arithmetic.NatPairing.unpair_l n).1)
    front replete branch hit

/-! `Bk_tail_cover` 是真实阶段对象的 eventual 版本。

一个代码只需从自己的 owner 阶段开始有代表；更早阶段由 `default` 填充，
不会把尚未出现的目标成员伪装成早期阶段的像。该结构正好允许实际迭代中
先选 owner，再沿单调分支 transport 到任意晚阶段。 -/
structure Bk_tail_system (C : Type u) (S : Nat → Type v) where
  stage : C → Nat
  decode : ∀ c, S (stage c)
  transport : ∀ {m n}, m ≤ n → S m → S n
  extend : ∀ c n, stage c ≤ n → S n
  extend_transport : ∀ c n (h : stage c ≤ n),
    extend c n h = transport h (decode c)
  default : ∀ n, S n

structure Bk_tail_cover (C : Type u) (S : Nat → Type v) (Y : Type w) where
  system : Bk_tail_system C S
  embed : ∀ n, S n → Y
  embed_coherent : ∀ {m n} (h : m ≤ n) (s : S m),
    embed n (system.transport h s) = embed m s
  embed_extend_coherent : ∀ c n (h : system.stage c ≤ n),
    embed n (system.extend c n h) = embed (system.stage c) (system.decode c)
  owner : ∀ y : Y, ∃ c, embed (system.stage c) (system.decode c) = y

theorem Bk_tail_system.schedule_l
    {C : Type u} {S : Nat → Type v} {B : Type q}
    (sys : Bk_tail_system C S) (enum : Nat → C) (slot : C → Nat → Nat)
    (replete : ∀ c k, k < slot c k ∧ sys.stage c ≤ slot c k ∧
      enum (slot c k) = c)
    (branch : B → Nat → Prop)
    (hit : ∀ b m c, ∃ k, m < slot c k ∧ branch b (slot c k)) :
    ∃ z : ∀ n, S n, ∀ b c, ∃ n, branch b n ∧
      enum n = c ∧ ∃ h : sys.stage (enum n) ≤ n,
        z n = sys.extend (enum n) n h := by
  let z : ∀ n, S n := fun n =>
    if h : sys.stage (enum n) ≤ n then
      sys.extend (enum n) n h
    else sys.default n
  refine ⟨z, ?_⟩
  intro b c
  obtain ⟨k, hmk, hbranch⟩ := hit b 0 c
  let n := slot c k
  have hnstage := (replete c k).2.1
  have hcode := (replete c k).2.2
  have henum : enum n = c := hcode
  have hcond : sys.stage (enum n) ≤ n := by simpa only [henum] using hnstage
  refine ⟨n, hbranch, henum, hcond, ?_⟩
  simp only [z, dif_pos hcond]

theorem Bk_tail_cover.condensation_l
    {C : Type u} {S : Nat → Type v} {Y : Type w} {B : Type q}
    (cover : Bk_tail_cover C S Y) (enum : Nat → C) (slot : C → Nat → Nat)
    (replete : ∀ c k, k < slot c k ∧ cover.system.stage c ≤ slot c k ∧
      enum (slot c k) = c)
    (branch : B → Nat → Prop)
    (hit : ∀ b m c, ∃ k, m < slot c k ∧ branch b (slot c k)) :
    ∃ z : ∀ n, S n, ∀ b y, ∃ n, branch b n ∧ ∃ c,
      cover.embed n (z n) = y ∧
        cover.embed (cover.system.stage c) (cover.system.decode c) = y := by
  obtain ⟨z, hz⟩ := cover.system.schedule_l enum slot replete branch hit
  refine ⟨z, ?_⟩
  intro b y
  obtain ⟨c, howner⟩ := cover.owner y
  obtain ⟨n, hbranch, henum, hstage, hextend⟩ := hz b c
  refine ⟨n, hbranch, c, ?_, howner⟩
  calc
    cover.embed n (z n) = cover.embed n (cover.system.extend (enum n) n hstage) := by rw [hextend]
    _ = cover.embed (cover.system.stage (enum n))
        (cover.system.decode (enum n)) :=
      cover.embed_extend_coherent (enum n) n hstage
    _ = cover.embed (cover.system.stage c) (cover.system.decode c) := by rw [henum]
    _ = y := howner

theorem Bk_tail_cover.condensation_countable_l
    {C : Type u} {S : Nat → Type v} {Y : Type w} {B : Type q}
    (cover : Bk_tail_cover C S Y) (count : Bk_countable C)
    (branch : B → Nat → Prop)
    (hit : ∀ b m c, ∃ k, m <
        count.tail_slot cover.system.stage c k ∧
      branch b (count.tail_slot cover.system.stage c k)) :
    ∃ z : ∀ n, S n, ∀ b y, ∃ n, branch b n ∧ ∃ c,
      cover.embed n (z n) = y ∧
        cover.embed (cover.system.stage c) (cover.system.decode c) = y := by
  exact cover.condensation_l
    (fun n => count.enum
      (YesMetaZFC.Logic.Arithmetic.NatPairing.unpair_l n).1)
    (fun c k => count.tail_slot cover.system.stage c k)
    (fun c k => by
      simpa only [Bk_countable.tail_slot] using
        count.tail_replete_l cover.system.stage c k)
    branch hit

end YesMetaZFC.SetTheory.LargeCardinal
