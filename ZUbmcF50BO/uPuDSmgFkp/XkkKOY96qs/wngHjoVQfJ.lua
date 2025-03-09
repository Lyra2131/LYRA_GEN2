-- Improved VisualEngine.lua
-- Visual Engine Module for 3D ESP (Line-based bounding box) with a universal skeleton overlay.
-- 
-- New Features for Performance:
--  • Uses Update3D and UpdateFOV functions that run every frame via RunService.RenderStepped.
--  • Only one set of drawing objects is created per character; duplicate drawings are avoided.
--  • ESP drawings are updated only if the on-screen (screen-space) center of the bounding box
--    changes by at least 1 pixel.
--  • Skeleton drawing is simplified to a universal system: 4 lines drawn from the bounding box
--    center to its top, bottom, left, and right midpoints.
--  • Drawings are cleaned up automatically when a character dies or is removed.
--
-- Usage:
--   VisualEngine:Start3D({
--       Object = "Players",                -- folder/service name ("Players")
--       Teams = true,                      -- skip teammates (if on the same team as the local player)
--       Color = Color3.new(1, 0, 0),         -- ESP color
--       Thickness = 2,                     -- constant line thickness
--       PriorityRender = false,            -- if false, do not render ESP when obstructed
--       ReapplyOnDeath = true,             -- reapply ESP after death
--       Skeleton = true,                   -- enable universal skeleton drawing
--   })
--
--   VisualEngine:StartFOV({ ... })  -- See below for FOV functionality.
--
--   To unload all ESP drawings:
--   VisualEngine:Unload()

local VisualEngine = {}
VisualEngine.ESPBoxes = {}  -- key: character instance, value: { Lines, SkeletonUniversal, Connections, LastScrCenter }
VisualEngine.Config = {}
VisualEngine.RefreshConnection = nil
VisualEngine.FOVConnection = nil
VisualEngine.FOVIndicator = nil
VisualEngine.FOVConfig = nil
VisualEngine.FOVEdges = nil

local Players = game:GetService("Players")
local RunService = game:GetService("RunService")

-- Wait until the local player and camera are available.
while not Players.LocalPlayer do wait() end
local localPlayer = Players.LocalPlayer
while not workspace.CurrentCamera do wait() end
local camera = workspace.CurrentCamera

---------------------------------
-- Helper Functions
---------------------------------

local function GetPosition(obj)
    if typeof(obj) == "Instance" and obj.Position then
        return obj.Position
    elseif typeof(obj) == "Vector3" then
        return obj
    end
    return nil
end

local function ComputeBoundingBoxCorners(cframe, size)
    local halfSize = size * 0.5
    local offsets = {
        Vector3.new(-halfSize.X, -halfSize.Y, -halfSize.Z),
        Vector3.new( halfSize.X, -halfSize.Y, -halfSize.Z),
        Vector3.new( halfSize.X, -halfSize.Y,  halfSize.Z),
        Vector3.new(-halfSize.X, -halfSize.Y,  halfSize.Z),
        Vector3.new(-halfSize.X,  halfSize.Y, -halfSize.Z),
        Vector3.new( halfSize.X,  halfSize.Y, -halfSize.Z),
        Vector3.new( halfSize.X,  halfSize.Y,  halfSize.Z),
        Vector3.new(-halfSize.X,  halfSize.Y,  halfSize.Z),
    }
    local corners = {}
    for i, offset in ipairs(offsets) do
         corners[i] = cframe:PointToWorldSpace(offset)
    end
    return corners
end

local function WorldToScreen(position)
    local screenPos, onScreen = camera:WorldToViewportPoint(position)
    return Vector2.new(screenPos.X, screenPos.Y), onScreen
end

local function CreateLine(color, thickness)
    local line = Drawing.new("Line")
    line.Color = color
    line.Thickness = thickness or 2
    line.Visible = true
    return line
end

local function IsObstructed(targetPos, character)
    local origin = camera.CFrame.Position
    local direction = (targetPos - origin)
    local raycastParams = RaycastParams.new()
    raycastParams.FilterType = Enum.RaycastFilterType.Blacklist
    raycastParams.FilterDescendantsInstances = {character, localPlayer.Character}
    local result = workspace:Raycast(origin, direction, raycastParams)
    return (result ~= nil)
end

-- Universal Skeleton: Using bounding box midpoints.
local function ComputeUniversalSkeleton(corners)
    -- corners[1..4]: bottom face; corners[5..8]: top face
    local topCenter = (corners[5] + corners[6] + corners[7] + corners[8]) / 4
    local bottomCenter = (corners[1] + corners[2] + corners[3] + corners[4]) / 4
    local leftCenter = (corners[1] + corners[4] + corners[5] + corners[8]) / 4
    local rightCenter = (corners[2] + corners[3] + corners[6] + corners[7]) / 4
    local center = (topCenter + bottomCenter) / 2
    -- Return four pairs of points: top->center, center->bottom, center->left, center->right
    return {
        {from = topCenter, to = center},
        {from = center, to = bottomCenter},
        {from = center, to = leftCenter},
        {from = center, to = rightCenter},
    }
end

---------------------------------
-- Cleanup Function
---------------------------------
function VisualEngine:CleanupCharacter(character)
    local esp = self.ESPBoxes[character]
    if esp then
        if esp.Connections then
            for _, conn in ipairs(esp.Connections) do
                if conn and conn.Disconnect then
                    pcall(function() conn:Disconnect() end)
                end
            end
        end
        for _, line in ipairs(esp.Lines or {}) do
            pcall(function() line:Remove() end)
        end
        if esp.SkeletonUniversal then
            for _, line in ipairs(esp.SkeletonUniversal) do
                pcall(function() line:Remove() end)
            end
        end
        self.ESPBoxes[character] = nil
    end
end

---------------------------------
-- 3D ESP Functions
---------------------------------
function VisualEngine:CreateESPForCharacter(character, config, player)
    if self.ESPBoxes[character] then
        self:CleanupCharacter(character)
    end

    config = config or {}
    local color = config.Color or Color3.new(1, 0, 0)
    local thickness = config.Thickness or 2
    local lines = {}
    for i = 1, 12 do
        table.insert(lines, CreateLine(color, thickness))
    end

    local espData = {
        Character = character,
        Lines = lines,
        Player = player,
        Connections = {},
        LastScrCenter = nil,
    }

    -- Instead of rig-specific skeletons, we use a universal skeleton with 4 lines.
    if config.Skeleton then
        local skeletonLines = {}
        for i = 1, 4 do
            table.insert(skeletonLines, CreateLine(color, thickness))
        end
        espData.SkeletonUniversal = skeletonLines
    end

    -- Setup cleanup connections.
    espData.Connections = {
        character.AncestryChanged:Connect(function(child, parent)
            if not parent then
                self:CleanupCharacter(character)
            end
        end)
    }
    local humanoid = character:FindFirstChild("Humanoid")
    if humanoid then
        table.insert(espData.Connections, humanoid.Died:Connect(function()
            self:CleanupCharacter(character)
        end))
    end

    self.ESPBoxes[character] = espData
end

-- Update3D is our new function to update ESP drawings.
function VisualEngine:Update3D()
    for character, esp in pairs(self.ESPBoxes) do
        if character and character.Parent and character:FindFirstChild("Humanoid") then
            local cframe, size = character:GetBoundingBox()
            local corners = ComputeBoundingBoxCorners(cframe, size)
            local scrCorners = {}
            local visible = false
            for i, corner in ipairs(corners) do
                local scrPos, onScreen = WorldToScreen(corner)
                scrCorners[i] = scrPos
                if onScreen then visible = true end
            end

            -- Skip update if not on-screen.
            if not visible then
                for _, line in ipairs(esp.Lines) do line.Visible = false end
                if esp.SkeletonUniversal then
                    for _, line in ipairs(esp.SkeletonUniversal) do line.Visible = false end
                end
            else
                -- Compute the screen-space center of the bounding box.
                local newCenter = (scrCorners[1] + scrCorners[2] + scrCorners[3] + scrCorners[4] +
                                    scrCorners[5] + scrCorners[6] + scrCorners[7] + scrCorners[8]) / 8
                if esp.LastScrCenter and (newCenter - esp.LastScrCenter).Magnitude < 1 then
                    -- If the center hasn't moved more than 1 pixel, skip updating.
                else
                    esp.LastScrCenter = newCenter

                    -- Update bounding box lines.
                    esp.Lines[1].From = scrCorners[1]; esp.Lines[1].To = scrCorners[2]
                    esp.Lines[2].From = scrCorners[2]; esp.Lines[2].To = scrCorners[3]
                    esp.Lines[3].From = scrCorners[3]; esp.Lines[3].To = scrCorners[4]
                    esp.Lines[4].From = scrCorners[4]; esp.Lines[4].To = scrCorners[1]
                    esp.Lines[5].From = scrCorners[5]; esp.Lines[5].To = scrCorners[6]
                    esp.Lines[6].From = scrCorners[6]; esp.Lines[6].To = scrCorners[7]
                    esp.Lines[7].From = scrCorners[7]; esp.Lines[7].To = scrCorners[8]
                    esp.Lines[8].From = scrCorners[8]; esp.Lines[8].To = scrCorners[5]
                    esp.Lines[9].From = scrCorners[1]; esp.Lines[9].To = scrCorners[5]
                    esp.Lines[10].From = scrCorners[2]; esp.Lines[10].To = scrCorners[6]
                    esp.Lines[11].From = scrCorners[3]; esp.Lines[11].To = scrCorners[7]
                    esp.Lines[12].From = scrCorners[4]; esp.Lines[12].To = scrCorners[8]
                    for _, line in ipairs(esp.Lines) do
                        line.Thickness = self.Config.Thickness or 2
                        line.Visible = true
                    end

                    -- Update universal skeleton if enabled.
                    if esp.SkeletonUniversal then
                        local uniConns = ComputeUniversalSkeleton(corners)
                        for i, conn in ipairs(uniConns) do
                            local line = esp.SkeletonUniversal[i]
                            local scrA, onA = WorldToScreen(conn.from)
                            local scrB, onB = WorldToScreen(conn.to)
                            line.From = scrA
                            line.To = scrB
                            line.Thickness = self.Config.Thickness or 2
                            line.Visible = onA and onB
                        end
                    end
                end
            end
        else
            self:CleanupCharacter(character)
        end
    end
end

function VisualEngine:StartESPRefresh()
    self.RefreshConnection = RunService.RenderStepped:Connect(function()
        self:Update3D()
    end)
end

function VisualEngine:Unload()
    if self.RefreshConnection then
        self.RefreshConnection:Disconnect()
        self.RefreshConnection = nil
    end
    if self.FOVConnection then
        self.FOVConnection:Disconnect()
        self.FOVConnection = nil
    end
    for character, esp in pairs(self.ESPBoxes) do
        self:CleanupCharacter(character)
    end
    self.ESPBoxes = {}
end

---------------------------------
-- FOV Functions
---------------------------------
-- StartFOV:
--   Args:
--     Place: "Mouse" or "Center" (default "Center")
--     Edges: "perfect" to use a Circle drawing, or a number (e.g. 10) for a polygon
--     Radius: FOV radius in pixels (default 100)
--     Thickness: Line thickness (default 1)
--     Color: Drawing color (default white)
function VisualEngine:StartFOV(config)
    config = config or {}
    self.FOVConfig = config

    self:StopFOV()

    if config.Edges and tostring(config.Edges):lower() == "perfect" then
        self.FOVIndicator = Drawing.new("Circle")
        self.FOVIndicator.Color = config.Color or Color3.new(1,1,1)
        self.FOVIndicator.Thickness = config.Thickness or 1
        self.FOVIndicator.Radius = config.Radius or 100
        self.FOVIndicator.Visible = true
        self.FOVIndicator.Filled = false
    else
        local edges = tonumber(config.Edges) or 10
        self.FOVEdges = edges
        self.FOVIndicator = {}
        for i = 1, edges do
            local line = CreateLine(config.Color or Color3.new(1,1,1), config.Thickness or 1)
            table.insert(self.FOVIndicator, line)
        end
    end

    if self.FOVConnection then self.FOVConnection:Disconnect() end
    self.FOVConnection = RunService.RenderStepped:Connect(function()
        self:UpdateFOV()
    end)
end

function VisualEngine:UpdateFOV()
    local config = self.FOVConfig or {}
    local pos
    if config.Place and config.Place:lower() == "mouse" then
        local mouse = localPlayer:GetMouse()
        pos = Vector2.new(mouse.X, mouse.Y)
    else
        pos = Vector2.new(camera.ViewportSize.X/2, camera.ViewportSize.Y/2)
    end

    if config.Edges and tostring(config.Edges):lower() == "perfect" then
        if self.FOVIndicator then
            self.FOVIndicator.Position = pos
        end
    else
        local edges = self.FOVEdges or 10
        local radius = config.Radius or 100
        local vertices = {}
        for i = 1, edges do
            local angle = math.rad((360/edges) * i)
            local vertex = pos + Vector2.new(math.cos(angle)*radius, math.sin(angle)*radius)
            vertices[i] = vertex
        end
        for i = 1, edges do
            local line = self.FOVIndicator[i]
            line.From = vertices[i]
            line.To = vertices[(i % edges) + 1]
        end
    end
end

function VisualEngine:StopFOV()
    if self.FOVConnection then
        self.FOVConnection:Disconnect()
        self.FOVConnection = nil
    end
    if self.FOVIndicator then
        if type(self.FOVIndicator) == "table" then
            for _, line in ipairs(self.FOVIndicator) do
                pcall(function() line:Remove() end)
            end
        else
            pcall(function() self.FOVIndicator:Remove() end)
        end
        self.FOVIndicator = nil
    end
end

---------------------------------
-- Main 3D ESP Initializer
---------------------------------
function VisualEngine:Start3D(config)
    self.Config = config or {}
    local source = self.Config.Object
    local sourceFolder

    while not workspace.CurrentCamera do wait() end
    camera = workspace.CurrentCamera

    if typeof(source) == "string" then
        if source == "Players" then
            sourceFolder = Players
        else
            sourceFolder = game:FindFirstChild(source)
        end
    elseif typeof(source) == "Instance" then
        sourceFolder = source
    else
        error("Invalid Object specified in VisualEngine:Start3D")
    end

    local function onCharacterAdded(character, player)
        if self.Config.Teams then
            if player.Team and localPlayer.Team and player.Team == localPlayer.Team then
                return
            end
        end
        character:WaitForChild("Humanoid", 5)
        if character then
            self:CreateESPForCharacter(character, self.Config, player)
            if self.Config.ReapplyOnDeath then
                local humanoid = character:FindFirstChild("Humanoid")
                if humanoid then
                    humanoid.Died:Connect(function()
                        self:CleanupCharacter(character)
                    end)
                end
            end
        end
    end

    if sourceFolder == Players then
        for _, player in ipairs(Players:GetPlayers()) do
            if player ~= localPlayer then
                if player.Character then
                    onCharacterAdded(player.Character, player)
                end
                player.CharacterAdded:Connect(function(character)
                    onCharacterAdded(character, player)
                end)
            end
        end
        Players.PlayerAdded:Connect(function(player)
            if player ~= localPlayer then
                player.CharacterAdded:Connect(function(character)
                    onCharacterAdded(character, player)
                end)
            end
        end)
    else
        for _, child in ipairs(sourceFolder:GetChildren()) do
            if child:IsA("Model") and child:FindFirstChild("Humanoid") then
                self:CreateESPForCharacter(child, self.Config)
                if self.Config.ReapplyOnDeath then
                    local humanoid = child:FindFirstChild("Humanoid")
                    if humanoid then
                        humanoid.Died:Connect(function()
                            self:CleanupCharacter(child)
                        end)
                    end
                end
            end
        end
    end

    self:StartESPRefresh()
end

return VisualEngine
